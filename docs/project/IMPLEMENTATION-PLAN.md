# BTC Miner implementation approach

29 September 2026 — requirements confirmed; version 1.2.0 implemented.

## Working scope and architecture

Build on the existing Python service, C SHA256d engine, and Terminal dashboard.
Keep THESIS2 as the default and prioritize its optimization. Use s to start and
t to stop. No public-network mining or automatic startup is part of the build. The first deliverable is a portable,
tested experimental miner, not a claim of profitability or THESIS2 speedup.

Preserve the current division of responsibilities:

- `settings.py`: validated configuration and atomic persistence.
- `protocol.py` / `serialization.py`: deterministic job and block construction.
- `native.py` / `native/hasher_fast.c`: bounded hashing batches.
- `connections.py` / `rpc.py`: node and pool communication.
- `engine.py`: scheduling, cancellation, validation, accounting, and submission.
- `service.py`: process lifecycle and local controls.
- `cli.py` / `tui.py`: user actions and presentation.
- `thesis2.py`: experimental traversal and mathematical diagnostics.

No framework rewrite is needed for the current Terminal product. If a graphical
app is selected, put it over the existing service interface after that interface
and its lifecycle have been validated. An ASIC controller requires new hardware
integration and is a separate product scope.

## Options, from most comprehensive to simplest

### A. Complete validated local miner

1. **Establish a repeatable build.** Stage only explicit source inputs, compile
   native code, run native self-tests and regression tests, sign locally, generate
   checksums, and package. Exclude machine settings, credentials, and session logs.
2. **Validate consensus construction.** Run an isolated Bitcoin Core regtest node
   with a temporary data directory and no public peers. Generate funding blocks,
   include a witness transaction, construct a block through this miner, solve it,
   submit it, and confirm its hash becomes the active tip. Exercise wrong-network
   and bad-cookie errors. Unit tests alone cannot certify block acceptance.
3. **Validate Stratum sessions.** Use a controlled local server for subscribe,
   authorization, target changes, extranonce changes, stale jobs, fragmented
   messages, rejects, lost responses, disconnects, and backup recovery. Then
   validate against the user's selected pool at a suitable share difficulty.
4. **Validate lifecycle behavior.** Test start/attach/stop/restart, repeated start,
   simultaneous commands, failed startup, crashes, watchdog limits, manual and
   activity pauses, interface close, sleep/wake, and bounded shutdown. A stop
   must prevent automatic restart and must preserve accurate session counters.
5. **Complete the selected user flow.** First launch → setup → validate connection
   → ready → explicit Start → connected/mining or paused → Stop → summary.
   Show separate states for invalid settings, unavailable node/pool, rejected
   authorization, and an unknown submission outcome. Keep closing behavior explicit.
6. **Measure and optimize.** Benchmark sustained full-engine throughput and
   responsiveness with default logging, both linear and THESIS2, at 1/2/4/8
   workers. Profile traversal generation and Python-to-C conversion. If justified,
   pass packed buffers or generate traversal batches in C, preserving byte-for-byte
   ordering and rank semantics against a Python reference. Retest final partial
   tiles, cancellation, resumption, and counts. Optimize based on measurements.
7. **Package the release.** Update status/help, test fresh extraction on the target
   Mac, document supported node/pool versions, and publish reproducible checks.
   Wider distribution may need Developer ID signing and notarization; current
   ad-hoc signing is for a local build and is not notarization.

Acceptance: Core accepts a constructed witness-containing block on regtest;
the selected pool accepts shares; failure/lifecycle tests pass; measured speed
includes strategy and diagnostic overhead; no silent lost work or misleading
acceptance counts. Test evidence reduces risk but cannot promise flawless behavior.

### B. Selected Core-first experimental release — implemented in version 1.2.0

1. Complete the build and offline regression foundation.
2. Prove block acceptance against an isolated Core regtest node.
3. Validate service start/stop/pause/restart and finish the Terminal setup flow.
4. Keep THESIS2 as default, optimize its native batches, and use linear as a performance reference.
5. Configure the user's intended Core connection and payout only after the
   connection/network checks pass. Keep mining opt-in.
6. Add pool validation and any new graphical interface as subsequent milestones.

This gives a smaller set of behaviors to validate first without removing existing
pool code. Existing pool support remains experimental until tested.

### C. Simplest usable deliverable — offline research/build package

1. Compile and verify the native library.
2. Run hash, protocol, traversal, scheduler, and message-handling regression checks.
3. Package the current Terminal application with inspect/benchmark commands.
4. Report precisely which integration paths remain unvalidated. Keep node and
   pool setup manual; do not advertise production readiness.

This was the version 1.1.1 milestone. Version 1.2.0 now includes the selected Core-first validation.

## Confirmed user requirements

1. Reliable experimental miner on this Mac.
2. Bitcoin Core first, beginning with isolated regtest validation.
3. Improve the existing Terminal dashboard.
4. THESIS2 remains the default, with optimization prioritized.
5. s starts and t stops.

The current close/idle policy is preserved: closing the view leaves an explicitly
started miner running, and keyboard/mouse activity pauses hashing until 120 seconds
idle. Use t to stop. No payout address or pool account was invented.

## Completed in version 1.2.0

- Native THESIS2 batch generation and packed-buffer hashing preserve the existing mapping.
- CRT reconstruction uses its exact modular identity; original Python formulas and
  generation remain reference checks. Partial-tile exhaustion and sample counts are tested.
- Diagnostic samples are filtered in C and written in batches with unchanged values.
- The real scheduler and default diagnostics are included in a new offline benchmark.
- Core accepted a THESIS2-constructed block containing a witness transaction on regtest.
- Concurrent starts, attach, pause/resume, restart, stop, malformed controls, and the
  Terminal start control passed against the disposable node.
- s opens setup when needed. t cancels pending worker changes and queues behind a
  busy command. Setup validates network/address/endpoint fields.
- Version 1.2.0 packaging includes source-matched validation evidence and 42 offline tests.

## User flow

Open the app → /setup (or s on an unconfigured install) → select Core, network,
payout address and node location → /doctor --connect → s → MINING or PAUSED →
t → STOPPED and session summary.

Setup does not start mining. Regtest validation uses disposable settings; configure
the node you intend to use before starting a normal session.

## Changes made for the initial build

- Exact Stratum target arithmetic, independent of Decimal context precision;
  decimal difficulty values retain their precision when decoded from the wire.
- Validation of local control-message shape and Boolean summary settings.
- Native-aware offline self-test, including fallback reporting, genesis nonce,
  inclusive target comparison, wraparound, and scanner/reference comparisons.
- Standard-library regression tests and a clean staged build/archive command.

Run `python3 -B scripts/build.py` to build. Run
`python3 -B -m unittest discover -s tests -v` for regression tests, and
`./bin/btc-miner self-test --require-native` for a quick native check.

## Evidence and remaining limits

See VALIDATION.md and validation/regtest.json. Core 31.1 regtest block acceptance
and service/Terminal checks passed. The original Bitcoin-Qt installation and its
data directory were not modified. Mainnet and real pool operation, long-running
thermal behavior, forced-crash watchdog recovery, system sleep/wake, and a THESIS2
statistical advantage remain unvalidated.

Reproduce Core checks with `python3 -B scripts/regtest.py --bitcoind /path/to/bitcoind`.
Measure the scheduler with `./bin/btc-miner benchmark --strategy thesis2 --seconds 3 --sweep`.

Protocol references:

- https://developer.bitcoin.org/reference/rpc/getblocktemplate.html
- https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki
- https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki
