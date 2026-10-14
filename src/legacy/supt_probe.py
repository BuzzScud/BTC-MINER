"""
Frozen SUPT-CA probe (alpha=0.01, zero free parameters).

Seven-step pipeline from Sheppard preprint Section 2. Diagnostic only —
does not alter nonce search order.
"""
from __future__ import annotations

import math
from datetime import datetime, timezone
from typing import Any, Optional

import supt_streams
from config import supt_data_dir

ALPHA = 0.01
MIN_VALUES = 3
# Jauncey & Langsdorf 4th-unit medium address (free-space impedance)
Z0_OHM = math.sqrt((4e-7 * math.pi) / 8.8541878128e-12)
PHI = (1 + math.sqrt(5)) / 2

ANCHORS: dict[str, dict[str, Any]] = {
    "solana_slot_timing": {"d_ij": 0.0447, "regime": "DEEP_LOCK", "label": "Solana slot timing"},
    "bitcoin_pow_clutch": {"d_ij": "1.0-2.0", "regime": "CLUTCH", "label": "Bitcoin PoW timing"},
    "ethereum_tx_window": {"d_ij": 0.673, "regime": "COHERENCE", "label": "Ethereum tx window"},
    "rsa_2048_baseline": {"d_ij": 0.6124, "regime": "COHERENCE", "label": "RSA-2048 baseline"},
    "falcon_secret_fg": {"d_ij": 0.042, "regime": "COHERENCE", "label": "Falcon secret f/g"},
}


def regime_label(d_ij: float) -> str:
    if d_ij < 0.5:
        return "DEEP_LOCK"
    if d_ij < 1.0:
        return "COHERENCE"
    if d_ij < 2.0:
        return "CLUTCH"
    if d_ij < 3.61:
        return "SUB_FLOOR"
    return "VACUUM"


def frozen_probe(
    values: list[float | int],
    *,
    window: Optional[int] = None,
) -> dict[str, Any]:
    """
    Apply frozen 7-step SUPT pipeline to an ordered sequence of positive values.
    """
    cleaned = [abs(float(v)) for v in values if v is not None and float(v) != 0.0]
    if window is not None and window > 0:
        cleaned = cleaned[-window:]
    n = len(cleaned)
    if n < MIN_VALUES:
        return {
            "ok": False,
            "error": f"need >= {MIN_VALUES} values",
            "n": n,
            "alpha": ALPHA,
            "length_matched": window is not None and n == window,
        }

    cleaned.sort()
    lg = [math.log10(x) for x in cleaned]
    gaps = [lg[i + 1] - lg[i] for i in range(len(lg) - 1)]
    mean_abs = sum(abs(g) for g in gaps) / len(gaps)
    if mean_abs == 0:
        return {
            "ok": False,
            "error": "zero gap mean",
            "n": n,
            "alpha": ALPHA,
            "length_matched": window is not None and n == window,
        }

    g_norm = [g / mean_abs for g in gaps]
    c: list[float] = [ALPHA * math.cos(2 * math.pi * g_norm[0])]
    for gi in g_norm[1:]:
        c.append(ALPHA * math.cos(2 * math.pi * gi) + (1 - ALPHA) * c[-1])

    tail_n = min(50, max(1, int(len(c) * 0.2)))
    mu = sum(abs(x) for x in c[-tail_n:]) / tail_n
    d_ij = -math.log(mu + 1e-12)
    u_max = max(math.exp(-abs(x)) for x in c)

    return {
        "ok": True,
        "d_ij": round(d_ij, 4),
        "u_max": round(u_max, 6),
        "regime": regime_label(d_ij),
        "n": n,
        "alpha": ALPHA,
        "length_matched": window is None or n == window,
    }


def _sequence_stream_a_hash_int() -> list[int]:
    rings = supt_streams.get_ring_buffers().get("hash_int", [])
    if len(rings) >= MIN_VALUES:
        return [int(x) for x in rings]
    vals = supt_streams.read_column_tail("a", "hash_int")
    return [int(v) for v in vals]


def _sequence_stream_b_column(column: str) -> list[float]:
    rings = supt_streams.get_ring_buffers()
    key = "hashes_tried" if column == "hashes_tried" else "seconds"
    ring_vals = rings.get(key, [])
    if len(ring_vals) >= MIN_VALUES:
        return [float(x) for x in ring_vals]
    return supt_streams.read_column_tail("b", column)


def _sequence_stream_b_nonce_found() -> list[float]:
    return supt_streams.read_column_tail("b", "nonce_found")


def _probe_named(name: str, values: list[float | int], window: int) -> dict[str, Any]:
    result = frozen_probe(values, window=window)
    result["name"] = name
    result["window"] = window
    return result


def anchor_z0(values: list[float | int]) -> list[float]:
    """Express values in units of Z0 (M.K.O.S. dimensioned-medium frame)."""
    return [float(v) / Z0_OHM for v in values]


def reference_phi_lattice(n: int = 41) -> list[float]:
    """Z0 * phi^n reference lattice."""
    return [Z0_OHM * (PHI ** i) for i in range(max(3, n))]


def reference_fib_ratios(n: int = 60) -> list[float]:
    """Z0 * Fibonacci consecutive ratios."""
    fib = [1, 1]
    while len(fib) < n + 1:
        fib.append(fib[-1] + fib[-2])
    return [Z0_OHM * fib[i + 1] / fib[i] for i in range(len(fib) - 1)]


def _collect_stream_probes(
    probes_raw: dict[str, Any],
    probes_z0: dict[str, Any],
    *,
    prefix: str,
    values: list[float | int],
    windows: list[int],
) -> None:
    anchored = anchor_z0(values)
    for w in windows:
        key = f"{prefix}_{w}"
        probes_raw[key] = _probe_named(key, values, w)
        z0_key = f"{prefix}_{w}"
        probes_z0[z0_key] = _probe_named(f"{z0_key}_z0", anchored, w)


def run_z0_probe_report(
    *,
    data_dir: Optional[str] = None,
    window_filter: str = "all",
    source_filter: str = "both",
) -> dict[str, Any]:
    """
    Frozen SUPT probe in raw and Z0-anchored frames, plus Z0 reference lattices.
    Diagnostic only — reads live Stream A/B CSV or in-memory rings.
    """
    _ = data_dir or supt_data_dir()

    stream_a = _sequence_stream_a_hash_int()
    stream_b_hashes = _sequence_stream_b_column("hashes_tried")
    stream_b_seconds = _sequence_stream_b_column("seconds")

    windows = [512, 71] if window_filter == "all" else [int(window_filter)]
    sources = ["stream_a", "stream_b"] if source_filter == "both" else [source_filter]

    probes_raw: dict[str, Any] = {}
    probes_z0: dict[str, Any] = {}

    if "stream_a" in sources or source_filter == "stream_a":
        _collect_stream_probes(
            probes_raw, probes_z0, prefix="stream_a_hash_int", values=stream_a, windows=windows
        )

    if "stream_b" in sources or source_filter == "stream_b":
        _collect_stream_probes(
            probes_raw,
            probes_z0,
            prefix="stream_b_seconds",
            values=stream_b_seconds,
            windows=windows,
        )
        _collect_stream_probes(
            probes_raw,
            probes_z0,
            prefix="stream_b_hashes_tried",
            values=stream_b_hashes,
            windows=windows,
        )

    phi_lattice = reference_phi_lattice()
    fib_lattice = reference_fib_ratios()

    insufficient = len(stream_b_hashes) < 71 or len(stream_b_seconds) < 71
    if len(stream_a) < 71:
        insufficient = True

    return {
        "ok": True,
        "z0_ohm": round(Z0_OHM, 4),
        "probes": {
            "raw": probes_raw,
            "z0_anchored": probes_z0,
        },
        "reference_lattice": {
            "z0_phi_powers": frozen_probe(phi_lattice),
            "z0_fib_ratios": frozen_probe(fib_lattice),
        },
        "anchors": ANCHORS,
        "insufficient_data": insufficient,
        "data_dir": supt_data_dir(),
        "sequence_lengths": {
            "stream_a_hash_int": len(stream_a),
            "stream_b_hashes_tried": len(stream_b_hashes),
            "stream_b_seconds": len(stream_b_seconds),
        },
        "interpretation": (
            "Raw probes match the dashboard frame. Z0-anchored probes divide each value by "
            f"Z0 ({Z0_OHM:.4f} ohm) before frozen_probe. Stream B seconds/hashes_tried are the "
            "consensus-timing cadence read; compare to BTC PoW anchor band 1.0-2.0 (CLUTCH)."
        ),
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }


def run_probe_report(
    *,
    data_dir: Optional[str] = None,
    window_filter: str = "all",
    source_filter: str = "both",
) -> dict[str, Any]:
    """Run length-matched probes at N=512 and N=71 for Stream A and Stream B."""
    _ = data_dir or supt_data_dir()
    probes: dict[str, Any] = {}

    stream_a = _sequence_stream_a_hash_int()
    stream_b_hashes = _sequence_stream_b_column("hashes_tried")
    stream_b_seconds = _sequence_stream_b_column("seconds")
    stream_b_nonces = _sequence_stream_b_nonce_found()

    windows = [512, 71] if window_filter == "all" else [int(window_filter)]
    sources = ["stream_a", "stream_b"] if source_filter == "both" else [source_filter]

    if "stream_a" in sources or source_filter == "stream_a":
        for w in windows:
            key = f"stream_a_hash_int_{w}"
            probes[key] = _probe_named(key, stream_a, w)

    if "stream_b" in sources or source_filter == "stream_b":
        for w in windows:
            probes[f"stream_b_hashes_tried_{w}"] = _probe_named(
                f"stream_b_hashes_tried_{w}", stream_b_hashes, w
            )
            probes[f"stream_b_seconds_{w}"] = _probe_named(
                f"stream_b_seconds_{w}", stream_b_seconds, w
            )
            if stream_b_nonces:
                probes[f"stream_b_nonce_found_{w}"] = _probe_named(
                    f"stream_b_nonce_found_{w}", stream_b_nonces, w
                )

    insufficient = len(stream_b_hashes) < 71 or len(stream_b_seconds) < 71
    if len(stream_a) < 71:
        insufficient = True

    return {
        "ok": True,
        "probes": probes,
        "anchors": ANCHORS,
        "insufficient_data": insufficient,
        "data_dir": supt_data_dir(),
        "sequence_lengths": {
            "stream_a_hash_int": len(stream_a),
            "stream_b_hashes_tried": len(stream_b_hashes),
            "stream_b_seconds": len(stream_b_seconds),
            "stream_b_nonce_found": len(stream_b_nonces),
        },
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }


def _probes_for_sequences(
    stream_a: list[float | int],
    stream_b_seconds: list[float | int],
    stream_b_hashes: list[float | int],
) -> dict[str, Any]:
    return {
        "stream_a_512": frozen_probe(stream_a, window=512),
        "stream_a_71": frozen_probe(stream_a, window=71),
        "stream_b_seconds_512": frozen_probe(stream_b_seconds, window=512),
        "stream_b_seconds_71": frozen_probe(stream_b_seconds, window=71),
        "stream_b_hashes_tried_512": frozen_probe(stream_b_hashes, window=512),
        "stream_b_hashes_tried_71": frozen_probe(stream_b_hashes, window=71),
    }


def run_compare_report() -> dict[str, Any]:
    """Side-by-side SUPT probes grouped by search_mode for A/B comparison."""
    mode_data = supt_streams.get_mode_buffers()
    round_counts = mode_data.get("round_counts", {})
    stream_a_samples = mode_data.get("stream_a_samples", {})
    result_modes: dict[str, Any] = {}
    notes: list[str] = []

    for mode in ("thesis2", "thesis", "linear", "hybrid"):
        stream_a = mode_data.get("hash_int", {}).get(mode, [])
        seconds = mode_data.get("seconds", {}).get(mode, [])
        hashes_tried = mode_data.get("hashes_tried", {}).get(mode, [])
        rounds = int(round_counts.get(mode, 0))
        result_modes[mode] = {
            "rounds": rounds,
            "stream_a_samples": int(stream_a_samples.get(mode, 0)),
            **_probes_for_sequences(stream_a, seconds, hashes_tried),
        }
        if rounds == 0:
            notes.append(f"{mode}: no rounds recorded yet")

    partial = any(result_modes[m]["rounds"] == 0 for m in ("thesis2", "linear"))
    note = "; ".join(notes) if notes else None

    return {
        "ok": True,
        "thesis2": result_modes["thesis2"],
        "thesis": result_modes["thesis"],
        "linear": result_modes["linear"],
        "hybrid": result_modes["hybrid"],
        "partial": partial,
        "note": note,
        "interpretation": "Diagnostic mode comparison. THESIS2 has its own samples; SUPT labels do not establish mining performance.",
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }
