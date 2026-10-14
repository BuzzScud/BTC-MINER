# Source notes

BTC engine/math extraction source:
`Downloads/GIT backup - 28sep/MINER-MAY-2026-main/backend/miner_server`.

Preserved modules: `thesis_mining`, `thesis_constants`, `supt_probe`, `supt_streams`,
`nonce_logger`, `log_utils`, and original RPC/config/backtest modules for provenance.
The new runtime uses its own validated settings, RPC, strategy scheduling and backtest
command; it does not launch the original web UI or multiprocessing coordinator.

`serialization.py` extracts Bitcoin serialization helpers from the original `miner_loop.py`.
`native/hasher_fast.c` is the original ARM SHA-256 implementation. The new bridge reports
exact scan counts, resumes a batch after pool shares, and bounds work for cancellation.

Legacy configuration has its built-in payout address removed and its worker default
reduced. Optional math lookup is package-relative. The mathematical formulas are retained.

Terminal behavior and Material colors follow the user's local `Desktop/PROJECTS/XMR MINER`
reference. This is an independent BTC control layer; no XMR hashing engine, fleet token,
Monero wallet, remote control or release machinery is included.

No behavioral testing was performed for the original 1.1.0 build. Version 1.1.1
adds offline regression coverage. Version 1.2.0 adds Core regtest integration.

## THESIS2 addition — version 1.1.0, 29 September 2026

The user-supplied `Desktop/thesis2-math-in-pictures.html` is bundled unchanged in
`reference/`. Its mathematical operations and corrections are ported to
`btcminer/thesis2.py`. Integer modular arithmetic and encoding use Python integers;
trigonometric and geometric diagnostics use floating point.

The HTML supplies mathematical primitives, not a Bitcoin nonce-search algorithm.
`Traversal` / `btc-traversal-v1` is a new application-defined composition of the field
cycle, coprime clock steps and CRT wheels into a nonce ordering. The geometry and
Gaussian encoding remain available through the math inspector. The legacy mining
math remains selectable through `thesis` and `hybrid`.

The HTML's theorem counts describe its source project. The underlying Lean proof
files are not included here. Neither this Python port nor its Bitcoin integration
inherits those proof claims. No implementation tests or performance measurements
were run for this addition, as requested. See `THESIS2 Implementation Report.html`
for the formula mapping, integration details, handoff and source digest.

## Offline build validation — version 1.1.1, 29 September 2026

Added standard-library regression tests for native hashing, nonce scan counts,
target boundaries, mathematical traversal, serialization, connection state,
local control parsing, and scheduler accounting. The original HTML implementation
report and the initial BUILD-ASSESSMENT.md are historical records; the current
build status is documented in README.md and IMPLEMENTATION-PLAN.md.

Fixed Stratum target rounding and malformed local control input handling. Added
native-aware self-tests and scripts/build.py for a clean tested package without
machine configuration or session logs. BIP173 public address test vectors are
referenced in tests/test_protocol.py; they are not runtime payout settings.

## Core validation and native traversal — version 1.2.0, 29 September 2026

Added C batch generation for the existing THESIS2 mapping, packed-buffer hashing,
and batch diagnostic persistence. Python traversal remains the reference. Tests
check the original CRT construction, tile boundaries, partial-tile exhaustion,
sampling values, and share resumption. No new nonce-prediction claim is introduced.

Added serialized service lifecycle controls, queued Terminal stop, setup validation,
full-engine offline benchmarks, and an isolated Core/Terminal integration harness.
The Core regtest report records source digests; the build checks these before
marking the packaged sources as validated. See VALIDATION.md for limitations.
