#!/usr/bin/env python3
"""
Backtest Python miner thesis nonce logic on the last N blocks (default 100).

Compares each block's actual nonce to the entropy-reduced minimal set and
`build_candidate_list` (thesis ordering). Reports phase1 / phase2 hits and misses.

Requires Bitcoin Core RPC (getblockhash, getblock). Run:
  python3 backtest_last_100_blocks.py [num_blocks]
  BTC_BACKTEST_BLOCKS=50 python3 backtest_last_100_blocks.py
"""
import os
import sys
from typing import Any, Callable, Optional

_here = os.path.dirname(os.path.abspath(__file__))
if _here not in sys.path:
    sys.path.insert(0, _here)

from config import load_config_from_env
from btc_rpc import getblockchaininfo, getblockhash, getblock, BitcoinRPCError
from thesis_mining import (
    bits_compact_to_difficulty_bits,
    nonce_generate_unified_py,
    nonce_generate_for_backtest,
    get_minimal_nonce_list,
    build_candidate_list,
    recovery_suggested_nonce,
)

NONCE_MASK = 0xFFFFFFFF
BACKTEST_BLOCKS_DEFAULT = 100
BACKTEST_BLOCKS_MIN = 1
BACKTEST_BLOCKS_MAX = 500


def _bits_hex_from_block(block: dict) -> str:
    """Normalize block 'bits' to 8-char hex string."""
    bits = block.get("bits")
    if bits is None:
        raise ValueError("block missing 'bits'")
    if isinstance(bits, str):
        return bits if len(bits) == 8 else bits.zfill(8)
    if isinstance(bits, int):
        return f"{bits:08x}"
    raise ValueError("block 'bits' must be str or int")


def _run_backtest(
    config: Any,
    num_blocks: int = BACKTEST_BLOCKS_DEFAULT,
    progress_callback: Optional[Callable[[int, int, Optional[dict]], None]] = None,
    overrides: Optional[dict] = None,
) -> dict:
    num_blocks = max(BACKTEST_BLOCKS_MIN, min(BACKTEST_BLOCKS_MAX, int(num_blocks)))
    info = getblockchaininfo(config)
    tip = int(info.get("blocks", -1))
    if tip < 0:
        raise ValueError("getblockchaininfo did not return 'blocks'")
    chain = info.get("chain", "unknown")

    if tip < 1:
        print("Chain has no blocks (tip=0). Nothing to backtest.")
        return {"phase1_hits": 0, "phase2_hits": 0, "misses": 0, "total": 0, "block_details": []}

    start_height = max(0, tip - num_blocks + 1)
    count = tip - start_height + 1
    heights = list(range(start_height, tip + 1))

    phase1_hits = 0
    phase2_hits = 0
    misses = 0
    simulated_hashes_when_found: list[int] = []
    distance_from_base: list[int] = []
    block_details: list[dict] = []

    for i, height in enumerate(heights):
        block_summary: Optional[dict] = None
        try:
            block_hash = getblockhash(config, height)
            block = getblock(config, block_hash, 1)
        except BitcoinRPCError as e:
            print(f"Block height {height}: RPC error {e}", file=sys.stderr)
            if progress_callback:
                progress_callback(i + 1, count, None)
            continue
        except Exception as e:
            print(f"Block height {height}: {e}", file=sys.stderr)
            if progress_callback:
                progress_callback(i + 1, count, None)
            continue

        actual_nonce = int(block.get("nonce", 0)) & NONCE_MASK
        bits_hex = _bits_hex_from_block(block)
        bits_int = int(bits_hex, 16)
        difficulty_bits = bits_compact_to_difficulty_bits(bits_int)
        bits_bytes = bytes.fromhex(bits_hex)

        if overrides:
            base_nonce = nonce_generate_for_backtest(height, difficulty_bits, overrides)
            recovery_nonce = recovery_suggested_nonce(bits_bytes)
            minimal_nonces = [base_nonce]
            if recovery_nonce is not None and recovery_nonce != base_nonce:
                minimal_nonces.append(recovery_nonce)
        else:
            base_nonce = nonce_generate_unified_py(height, difficulty_bits)
            minimal_nonces = get_minimal_nonce_list(height, difficulty_bits, bits_bytes)
            recovery_nonce = recovery_suggested_nonce(bits_bytes)
        recovery_nonce_val = recovery_nonce if recovery_nonce is not None else base_nonce
        candidates = build_candidate_list(
            base_nonce,
            recovery_nonce_val,
            0,
            0xFFFFFFFF + 1,
            block_height=height,
        )

        dist = abs((actual_nonce - base_nonce) & NONCE_MASK)
        distance_from_base.append(dist)

        hit_type = "miss"
        simulated_hashes: Optional[int] = None

        if actual_nonce in minimal_nonces:
            phase1_hits += 1
            idx = minimal_nonces.index(actual_nonce)
            sim = idx + 1
            simulated_hashes_when_found.append(sim)
            hit_type = "phase1"
            simulated_hashes = sim
        elif actual_nonce in candidates:
            phase2_hits += 1
            pos = candidates.index(actual_nonce)
            sim = len(minimal_nonces) + pos + 1
            simulated_hashes_when_found.append(sim)
            hit_type = "phase2"
            simulated_hashes = sim
        else:
            misses += 1

        block_summary = {
            "height": height,
            "actual_nonce": actual_nonce,
            "base_nonce": base_nonce,
            "recovery_nonce": recovery_nonce_val if recovery_nonce is not None else None,
            "hit_type": hit_type,
            "simulated_hashes": simulated_hashes,
            "distance_from_base": dist,
        }
        block_details.append(block_summary)

        if progress_callback:
            progress_callback(i + 1, count, block_summary)

    total = phase1_hits + phase2_hits + misses
    avg_hashes = (
        sum(simulated_hashes_when_found) / len(simulated_hashes_when_found)
        if simulated_hashes_when_found else 0
    )
    avg_distance = sum(distance_from_base) / len(distance_from_base) if distance_from_base else 0

    result: dict = {
        "chain": chain,
        "tip": tip,
        "start_height": start_height,
        "count": count,
        "phase1_hits": phase1_hits,
        "phase2_hits": phase2_hits,
        "misses": misses,
        "total": total,
        "simulated_hashes_when_found": simulated_hashes_when_found,
        "avg_hashes_when_found": avg_hashes,
        "min_hashes_when_found": min(simulated_hashes_when_found) if simulated_hashes_when_found else None,
        "max_hashes_when_found": max(simulated_hashes_when_found) if simulated_hashes_when_found else None,
        "avg_distance_from_base": avg_distance,
        "block_details": block_details,
    }
    if overrides:
        result["overrides"] = overrides
    return result


def main() -> int:
    config = load_config_from_env()
    raw_nb = os.environ.get("BTC_BACKTEST_BLOCKS", "").strip()
    if len(sys.argv) >= 2 and sys.argv[1].strip().isdigit():
        num_blocks = int(sys.argv[1].strip())
    elif raw_nb.isdigit():
        num_blocks = int(raw_nb)
    else:
        num_blocks = BACKTEST_BLOCKS_DEFAULT
    print(f"Backtest last {num_blocks} blocks (Bitcoin Core RPC)...")
    try:
        result = _run_backtest(config, num_blocks=num_blocks)
    except BitcoinRPCError as e:
        print(f"RPC error: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    if result["total"] == 0:
        return 0

    print(f"Chain: {result['chain']}, tip: {result['tip']}, blocks: {result['start_height']}..{result['tip']} (n={result['count']})")
    print(f"Phase 1 hits: {result['phase1_hits']}/{result['total']}")
    print(f"Phase 2 hits: {result['phase2_hits']}/{result['total']}")
    print(f"Misses: {result['misses']}/{result['total']}")
    if result["simulated_hashes_when_found"]:
        print(f"Avg simulated hashes when found: {result['avg_hashes_when_found']:.1f}")
        if result["min_hashes_when_found"] is not None:
            print(f"Min simulated hashes when found: {result['min_hashes_when_found']}")
        if result["max_hashes_when_found"] is not None:
            print(f"Max simulated hashes when found: {result['max_hashes_when_found']}")
    print(f"Avg |actual_nonce - base_nonce|: {result['avg_distance_from_base']:.0f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
