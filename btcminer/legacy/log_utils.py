"""Bounded log rotation and tail reads for miner data files."""
from __future__ import annotations

import os
from datetime import datetime, timezone
from typing import Optional

DEFAULT_MAX_LOG_BYTES = 5 * 1024 * 1024
DEFAULT_MAX_ARCHIVES = 2


def refresh_file_if_oversized(path: str, *, max_bytes: int) -> bool:
    """Delete an oversized log file so the next write starts fresh (no archives kept)."""
    if not path or not os.path.isfile(path):
        return False
    try:
        if os.path.getsize(path) <= max_bytes:
            return False
    except OSError:
        return False
    directory = os.path.dirname(path) or "."
    base_name = os.path.basename(path)
    name, ext = os.path.splitext(base_name)
    try:
        os.remove(path)
    except OSError:
        try:
            with open(path, "w", encoding="utf-8"):
                pass
        except OSError:
            return False
    prune_archives(directory, f"{name}.", ext, keep=0)
    return True


def rotate_file_if_oversized(
    path: str,
    *,
    max_bytes: int = DEFAULT_MAX_LOG_BYTES,
    keep_archives: int = DEFAULT_MAX_ARCHIVES,
) -> None:
    """Rename oversized file to a timestamped archive and prune older archives."""
    if not path or not os.path.isfile(path):
        return
    try:
        if os.path.getsize(path) <= max_bytes:
            return
    except OSError:
        return
    directory = os.path.dirname(path) or "."
    base_name = os.path.basename(path)
    name, ext = os.path.splitext(base_name)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    rotated = os.path.join(directory, f"{name}.{ts}{ext}")
    try:
        os.rename(path, rotated)
    except OSError:
        return
    prune_archives(directory, f"{name}.", ext, keep=keep_archives)


def prune_archives(directory: str, prefix: str, ext: str, *, keep: int = DEFAULT_MAX_ARCHIVES) -> None:
    """Keep only the newest `keep` rotated files matching prefix.*ext."""
    if keep < 0:
        return
    rotated: list[tuple[float, str]] = []
    try:
        names = os.listdir(directory)
    except OSError:
        return
    for fn in names:
        if not fn.startswith(prefix) or not fn.endswith(ext):
            continue
        full = os.path.join(directory, fn)
        if not os.path.isfile(full):
            continue
        try:
            rotated.append((os.path.getmtime(full), full))
        except OSError:
            continue
    rotated.sort(reverse=True)
    for _, old_path in rotated[keep:]:
        try:
            os.remove(old_path)
        except OSError:
            pass


def read_tail_lines(path: str, max_lines: int) -> list[str]:
    """Read the last N lines of a text file without loading the entire file."""
    if max_lines <= 0 or not os.path.isfile(path):
        return []
    try:
        size = os.path.getsize(path)
        if size <= 0:
            return []
    except OSError:
        return []
    chunk_size = 8192
    data = b""
    try:
        with open(path, "rb") as f:
            pos = size
            while pos > 0 and data.count(b"\n") <= max_lines:
                read_size = min(chunk_size, pos)
                pos -= read_size
                f.seek(pos)
                data = f.read(read_size) + data
        lines = data.decode("utf-8", errors="replace").splitlines()
        return lines[-max_lines:]
    except OSError:
        return []
