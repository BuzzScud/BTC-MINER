"""
SUPT dual-stream CSV logging (Stream A: raw hash search, Stream B: block cadence fold).

Format matches BTC STUFF / supt_miner.py for frozen-probe analysis.
"""
from __future__ import annotations

import csv
import json
import os
import queue
import threading
import time
from collections import deque
from datetime import datetime, timezone
from typing import Any, Optional

from config import normalize_search_mode, supt_data_dir, supt_logging_enabled, supt_sample_every
from log_utils import prune_archives, rotate_file_if_oversized, read_tail_lines

_STREAM_A_NAME = "nonce_hash_stream.csv"
_STREAM_B_NAME = "block_cadence.csv"
_SEARCH_MODE_LOG = "search_mode.jsonl"
_MAX_FILE_BYTES = 10 * 1024 * 1024
_MAX_ROTATED_FILES = 2
_RING_MAX = 512

_lock = threading.Lock()
_round_counter = 0
_active_rounds: dict[int, dict[str, Any]] = {}
_stream_a_rows = 0
_stream_b_rows = 0
_active_search_mode = "thesis"

# In-memory ring buffers for fast SUPT probe reads (Phase 3)
_hash_int_ring: deque[int] = deque(maxlen=_RING_MAX)
_hashes_tried_ring: deque[int] = deque(maxlen=_RING_MAX)
_seconds_ring: deque[float] = deque(maxlen=_RING_MAX)

# Per search_mode buffers for A/B comparison (Phase 4)
_mode_hash_int: dict[str, deque[int]] = {
    "thesis2": deque(maxlen=_RING_MAX),
    "thesis": deque(maxlen=_RING_MAX),
    "linear": deque(maxlen=_RING_MAX),
    "hybrid": deque(maxlen=_RING_MAX),
}
_mode_hashes_tried: dict[str, deque[int]] = {
    "thesis2": deque(maxlen=_RING_MAX),
    "thesis": deque(maxlen=_RING_MAX),
    "linear": deque(maxlen=_RING_MAX),
    "hybrid": deque(maxlen=_RING_MAX),
}
_mode_seconds: dict[str, deque[float]] = {
    "thesis2": deque(maxlen=_RING_MAX),
    "thesis": deque(maxlen=_RING_MAX),
    "linear": deque(maxlen=_RING_MAX),
    "hybrid": deque(maxlen=_RING_MAX),
}
_mode_round_counts: dict[str, int] = {"thesis2": 0, "thesis": 0, "linear": 0, "hybrid": 0}
_mode_stream_a_samples: dict[str, int] = {"thesis2": 0, "thesis": 0, "linear": 0, "hybrid": 0}

# MP worker samples -> main-thread writer
_sample_queue: queue.Queue[tuple[int, int, bytes] | None] = queue.Queue()
_writer_thread: Optional[threading.Thread] = None
_writer_stop = threading.Event()


def _stream_a_path() -> str:
    return os.path.join(supt_data_dir(), _STREAM_A_NAME)


def _stream_b_path() -> str:
    return os.path.join(supt_data_dir(), _STREAM_B_NAME)


def _search_mode_log_path() -> str:
    return os.path.join(supt_data_dir(), _SEARCH_MODE_LOG)


def set_active_search_mode(mode: str) -> None:
    """Set search mode for current mining session (thesis | linear | hybrid)."""
    global _active_search_mode
    with _lock:
        _active_search_mode = normalize_search_mode(mode)


def get_active_search_mode() -> str:
    with _lock:
        return _active_search_mode


def _ensure_data_dir() -> None:
    d = supt_data_dir()
    if d and not os.path.isdir(d):
        os.makedirs(d, exist_ok=True)


def _maybe_rotate(path: str) -> None:
    if not os.path.isfile(path):
        return
    rotate_file_if_oversized(
        path,
        max_bytes=_MAX_FILE_BYTES,
        keep_archives=_MAX_ROTATED_FILES,
    )
    directory = os.path.dirname(path) or "."
    base_name = os.path.basename(path)
    name, ext = os.path.splitext(base_name)
    prune_archives(directory, f"{name}.", ext, keep=_MAX_ROTATED_FILES)


def _write_header_if_new(path: str, header: list[str]) -> None:
    if os.path.isfile(path) and os.path.getsize(path) > 0:
        return
    _ensure_data_dir()
    with open(path, "w", newline="", encoding="utf-8") as f:
        csv.writer(f).writerow(header)


def _append_stream_a(block_id: int, nonce: int, hash_bytes: bytes, *, search_mode: Optional[str] = None) -> None:
    _append_stream_a_batch(block_id, [(nonce,hash_bytes)], search_mode=search_mode)


def _append_stream_a_batch(block_id, samples, *, search_mode=None):
    global _stream_a_rows
    if not supt_logging_enabled():
        return
    rows = [[block_id,nonce,int.from_bytes(digest,"little")] for nonce,digest in samples]
    if not rows:
        return
    mode = normalize_search_mode(search_mode or _active_search_mode)
    with _lock:
        for _,_,hash_int in rows:
            _hash_int_ring.append(hash_int)
            if mode in _mode_hash_int:
                _mode_hash_int[mode].append(hash_int)
        rnd = _active_rounds.get(block_id)
        if rnd is not None:
            rnd["stream_a_samples"] = rnd.get("stream_a_samples", 0) + len(rows)
        path = _stream_a_path()
        _maybe_rotate(path)
        _write_header_if_new(path, ["block", "nonce", "hash_int"])
        with open(path, "a", newline="", encoding="utf-8") as f:
            csv.writer(f).writerows(rows)
        _stream_a_rows += len(rows)


def _append_stream_b(
    block_id: int,
    nonce_found: int,
    hashes_tried: int,
    seconds: float,
    *,
    search_mode: Optional[str] = None,
) -> None:
    global _stream_b_rows
    if not supt_logging_enabled():
        return
    mode = normalize_search_mode(search_mode or _active_search_mode)
    with _lock:
        _hashes_tried_ring.append(hashes_tried)
        _seconds_ring.append(seconds)
        if mode in _mode_hashes_tried:
            _mode_hashes_tried[mode].append(hashes_tried)
            _mode_seconds[mode].append(seconds)
            _mode_round_counts[mode] = _mode_round_counts.get(mode, 0) + 1
        rnd = _active_rounds.pop(block_id, None)
        stream_a_samples = rnd.get("stream_a_samples", 0) if rnd else 0
        if mode in _mode_stream_a_samples:
            _mode_stream_a_samples[mode] = _mode_stream_a_samples.get(mode, 0) + stream_a_samples
    path = _stream_b_path()
    _maybe_rotate(path)
    _write_header_if_new(path, ["block", "nonce_found", "hashes_tried", "seconds"])
    with _lock:
        with open(path, "a", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow([block_id, nonce_found, hashes_tried, round(seconds, 6)])
        _stream_b_rows += 1
    _write_search_mode_log(
        block_id,
        mode,
        nonce_found,
        hashes_tried,
        seconds,
        stream_a_samples,
    )


def _write_search_mode_log(
    round_id: int,
    search_mode: str,
    nonce_found: int,
    hashes_tried: int,
    seconds: float,
    stream_a_samples: int,
) -> None:
    if not supt_logging_enabled():
        return
    _ensure_data_dir()
    entry = {
        "round_id": round_id,
        "search_mode": search_mode,
        "nonce_found": nonce_found,
        "hashes_tried": hashes_tried,
        "seconds": round(seconds, 6),
        "stream_a_samples": stream_a_samples,
        "ts": datetime.now(timezone.utc).isoformat(),
    }
    try:
        with open(_search_mode_log_path(), "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
    except OSError:
        pass


def _writer_loop() -> None:
    while not _writer_stop.is_set():
        try:
            item = _sample_queue.get(timeout=0.25)
        except queue.Empty:
            continue
        if item is None:
            break
        block_id, nonce, hash_bytes = item
        sample_every = supt_sample_every()
        if nonce % sample_every == 0:
            _append_stream_a(block_id, nonce, hash_bytes)


def _ensure_writer_thread() -> None:
    global _writer_thread
    if _writer_thread is not None and _writer_thread.is_alive():
        return
    _writer_stop.clear()
    _writer_thread = threading.Thread(target=_writer_loop, daemon=True, name="supt-stream-writer")
    _writer_thread.start()


def is_enabled() -> bool:
    return supt_logging_enabled()


def begin_round(height: int, *, search_mode: Optional[str] = None) -> int:
    """Start a mining round; returns session round id (Stream A/B block column)."""
    global _round_counter
    if not supt_logging_enabled():
        return -1
    _ensure_writer_thread()
    mode = normalize_search_mode(search_mode or _active_search_mode)
    with _lock:
        _round_counter += 1
        round_id = _round_counter
        _active_rounds[round_id] = {
            "height": height,
            "started": time.time(),
            "search_mode": mode,
            "stream_a_samples": 0,
        }
    return round_id


def sample_hash(round_id: int, nonce: int, hash_bytes: bytes) -> None:
    """Record hash sample for Stream A when nonce % sample_every == 0."""
    if round_id < 0 or not supt_logging_enabled():
        return
    sample_every = supt_sample_every()
    if nonce % sample_every != 0:
        return
    # Same process: write directly; workers should use enqueue_sample
    _append_stream_a(round_id, nonce, hash_bytes)


def sample_hashes(round_id, samples):
    """Persist one bounded scan's diagnostics with one file write operation."""
    if round_id < 0 or not supt_logging_enabled():
        return
    step = supt_sample_every()
    _append_stream_a_batch(round_id, ((n,h) for n,h in samples if n % step == 0))


def enqueue_sample(round_id: int, nonce: int, hash_bytes: bytes) -> None:
    """Queue sample from worker process (MP path)."""
    if round_id < 0 or not supt_logging_enabled():
        return
    if nonce % supt_sample_every() != 0:
        return
    _ensure_writer_thread()
    try:
        _sample_queue.put_nowait((round_id, nonce, bytes(hash_bytes)))
    except queue.Full:
        pass


def end_round(round_id: int, nonce_found: int, hashes_tried: int, elapsed_sec: float) -> None:
    """Append Stream B cadence row for completed round."""
    if round_id < 0 or not supt_logging_enabled():
        return
    with _lock:
        rnd = _active_rounds.get(round_id)
        mode = rnd.get("search_mode", _active_search_mode) if rnd else _active_search_mode
    _append_stream_b(round_id, nonce_found, hashes_tried, elapsed_sec, search_mode=mode)


def get_paths() -> dict[str, str]:
    return {
        "stream_a": _stream_a_path(),
        "stream_b": _stream_b_path(),
        "data_dir": supt_data_dir(),
    }


def get_recent_row_counts() -> dict[str, int]:
    with _lock:
        return {
            "stream_a_rows": _stream_a_rows,
            "stream_b_rows": _stream_b_rows,
        }


def get_status() -> dict[str, Any]:
    paths = get_paths()
    counts = get_recent_row_counts()
    return {
        "enabled": is_enabled(),
        "sample_every": supt_sample_every(),
        "stream_a_path": paths["stream_a"],
        "stream_b_path": paths["stream_b"],
        "stream_a_rows": counts["stream_a_rows"],
        "stream_b_rows": counts["stream_b_rows"],
    }


def tail_csv(which: str, lines: int = 5) -> list[list[str]]:
    """Return last N data rows from stream_a or stream_b (excluding header)."""
    path = _stream_a_path() if which == "a" else _stream_b_path()
    if not os.path.isfile(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            header = next(csv.reader([f.readline()]), None)
        if not header:
            return []
        tail_raw = read_tail_lines(path, max(lines + 1, 2))
        parsed = list(csv.reader(tail_raw))
        data = [row for row in parsed if row and row != header]
        return data[-lines:]
    except OSError:
        return []


def read_column_tail(which: str, column: str, max_rows: Optional[int] = None) -> list[float]:
    """Read numeric column from stream CSV (last max_rows values, bounded)."""
    cap = max_rows if max_rows is not None and max_rows > 0 else _RING_MAX
    path = _stream_a_path() if which == "a" else _stream_b_path()
    if not os.path.isfile(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            if reader.fieldnames is None or column not in reader.fieldnames:
                return []
            vals: deque[float] = deque(maxlen=cap)
            for row in reader:
                raw = row.get(column, "").strip()
                if not raw:
                    continue
                if column == "nonce_found" and raw == "-1":
                    continue
                try:
                    vals.append(float(raw))
                except ValueError:
                    continue
            return list(vals)
    except OSError:
        return []


def get_mode_buffers() -> dict[str, Any]:
    """Per search_mode sequences and round counts for SUPT A/B comparison."""
    with _lock:
        return {
            "hash_int": {k: list(v) for k, v in _mode_hash_int.items()},
            "hashes_tried": {k: list(v) for k, v in _mode_hashes_tried.items()},
            "seconds": {k: list(v) for k, v in _mode_seconds.items()},
            "round_counts": dict(_mode_round_counts),
            "stream_a_samples": dict(_mode_stream_a_samples),
        }


def get_ring_buffers() -> dict[str, list]:
    """Recent in-memory sequences for SUPT probe (Phase 3)."""
    with _lock:
        return {
            "hash_int": list(_hash_int_ring),
            "hashes_tried": list(_hashes_tried_ring),
            "seconds": list(_seconds_ring),
        }


def shutdown_writer() -> None:
    """Stop background writer thread (tests)."""
    _writer_stop.set()
    try:
        _sample_queue.put_nowait(None)
    except queue.Full:
        pass
