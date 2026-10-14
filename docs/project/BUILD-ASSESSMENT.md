# BTC MINER — build feasibility assessment

Date: 29 September 2026

## Verdict

Yes. This is an existing, buildable Apple Silicon miner prototype, with Python application code and a C SHA256d engine. The native source rebuilt successfully on this machine. It still needs integration validation before being described as a reliable mining application. No evidence here establishes a THESIS2 mining advantage or profitability.

## Existing implementation

- Terminal dashboard and macOS Terminal launcher.
- Project-local supervisor, controls, session summaries, and logs.
- Bitcoin Core RPC block construction/submission and Stratum V1 pool support.
- Native ARM SHA256d hashing and Python fallback.
- Linear, legacy thesis, hybrid, and THESIS2 search strategies.
- Bundled mathematical reference and source provenance notes.

The .app opens Terminal; it is not a native graphical dashboard. Python 3.9+ is required. Optional original C math/recovery libraries are missing, but disabled by default and not required for the default implementation. Lean proof artifacts are absent.

## Checks actually performed

Environment: arm64, macOS 15.1.1, Python 3.9.6, Apple clang 16, eight logical CPUs.

- Compiled every Python source in memory: passed.
- Rebuilt and ad-hoc signed the native library in a temporary directory: passed; packaged library preserved.
- CLI doctor and Python Bitcoin genesis hash self-test: passed.
- Compared both packaged and rebuilt native libraries with Python hashlib: each passed 101 header hash vectors, 606 scanner comparisons, and a genesis winning-nonce search.
- THESIS2: verified a complete 144,000-offset permutation for each of the 35 qualifying primes; verified 360 unique field points, first 1,000 traversal ranks, and sampled full/partial-tile ranks. Did not enumerate all 2^32 nonces or prove the complete math port.
- All 46 entries in FILES.sha256.json matched.

Short offline raw-hashing benchmark (one second per worker count):

| Workers | Million hashes/second |
| --- | ---: |
| 1 | 15.1 |
| 2 | 30.5 |
| 4 | 58.8 |
| 8 | 87.3 |

A separate one-second, single-thread comparison including candidate generation measured linear at 15.7 MH/s and THESIS2 at 3.7 MH/s. These are brief observations, not sustained thermal or full-engine measurements. Logging, network communication, submission, and dashboard overhead were excluded. THESIS2 currently incurs substantial Python candidate-generation/list-conversion overhead.

## Gaps before dependable use

1. Configure a payout address and either Bitcoin Core or a compatible pool. The folder has no machine.local.json; doctor found no cookie at the default Core location. This does not establish whether a node exists elsewhere.
2. Verify complete block construction and acceptance against Bitcoin Core regtest, including witness transactions.
3. Test Stratum handshake, share acceptance/rejection, difficulty updates, stale jobs, disconnects, and reconnects with a controlled server and then the intended pool.
4. Exercise supervisor start/stop/restart, idle pausing, shutdown, and the Terminal UI.
5. Add repeatable regression coverage. The built-in self-test checks only Python's genesis hash; it does not validate native hashing or integration.
6. Measure sustained full-engine throughput with default diagnostics. Optimize THESIS2 candidate generation if retaining it as the default.

THESIS2 is an application-defined nonce ordering assembled from the reference math. Tile permutation checks support its coverage design; they do not show that earlier candidates are more likely to meet a Bitcoin target. No head-to-head mining advantage has been established.

Recommended next implementation milestone: a reproducible offline regression harness plus a Bitcoin Core regtest acceptance test, followed by pool and lifecycle validation. Use linear search as the performance baseline.

No live mining session, pool submission, node RPC connection, GUI launch, or configuration change was performed. Existing source and packaged binaries were left unchanged; this report is the only added project file.

Protocol reference: https://developer.bitcoin.org/devguide/mining.html
