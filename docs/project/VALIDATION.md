# Validation scope and history

## Current release gate — October 7, 2026

The [master plan](MASTER_PLAN.md) defines source/object/assumption admission and
isolated packaging. The [portable proof report](../../research/proof-evidence/report.html)
binds 299 audited roots and 123 named statements across the repaired six-module
closure. Five exact closed-Nat products have supported executable translations.
These proofs do not establish full runtime refinement or SHA search reduction.

The earlier October 7 runtime baseline recorded 213 tests. Test totals and optional
solver skips depend on the environment; each new build records its own regression
log. Newly added proof admission and release tests MUST pass as part of packaging.
The full research workspace retains the current isolated results under
`validation/release-integration-20261007/`; each ZIP includes its own
`BUILD-INFO.json` and `validation/package-regression.log`. Source metadata refresh does not renew historical
Core, performance or deployment evidence. An accepted package does not restart or
change the active miner.

```sh
python3 -B scripts/verify_proof_evidence.py
python3 -B scripts/build.py
```

## Historical version 1.2.4 evidence

The remainder describes historical runs and limits at that revision, not the
current test inventory or present proof status.

Validated on this arm64 Mac, macOS 15.1.1, Python 3.9.6, Apple clang 16.

## Offline regression suite

The historical package passed 115 tests. Coverage includes native SHA256d against hashlib, genesis proof
of work, target boundaries, exact difficulty conversion, nonce scan counts and
wraparound, address validation, block serialization, witness/txid merkle handling,
THESIS2 tile permutations and native/Python ordering, partial-tile exhaustion,
diagnostic sample preservation, share outcome accounting, stale work, local
control validation, and Terminal `s`/`t` handling including queued stop.

Network-selection checks cover saved connection round trips, address/authentication
separation, preserving worker preferences, stop failure before any configuration
write, invalid profiles, distinct testnet3/testnet4 ports, and dashboard routing and
footer display. Service-start functions are forbidden by the network tests.

The Ember suite includes 14 layout tests, including the regtest multiplier, compact stopped-session labels
and simultaneous pause/queued-stop notices. Fixture-backed PTY checks cover resize,
palette/help and terminal restoration after q, Ctrl+C, SIGHUP and SIGTERM. The
extracted ZIP's source hashes, executable permissions, app signature and basic CLI
commands are verified. See `EMBER-IMPLEMENTATION.md` for reproducible checks.

```
python3 -B -m unittest discover -s tests -v
./bin/btc-miner self-test --require-native
```

## Bitcoin Core and Terminal integration

Version 1.2.4's `scripts/regtest.py` passed
against Bitcoin Core 31.1.0 with public peers disabled
and a temporary node data directory. The downloaded arm64 command-line archive
matched the SHA-256 published at https://bitcoincore.org/bin/bitcoin-core-31.1/SHA256SUMS.
No claim of independent PGP signature verification is made.

- A THESIS2-constructed and solved block containing a witness transaction was
  accepted as the active chain tip.
- Core accepted a block using a local ×256 target. Independent hashlib verification
  confirmed the stricter proof of work; the block's consensus nBits was unchanged.
- Difficulty up/down/numeric/reset controls did not start a stopped miner. Live
  changes to ×256, ×512, ×256 and ×1 restarted with the matching status multiplier
  and produced Core-accepted blocks.
- Simultaneous difficulty commands serialized without losing an update, both
  stopped and running. Invalid inputs and setting the current value preserved
  the running PID. Both multiplier limits and the regtest/testnet4 profile round
  trip were checked through the actual CLI.
- Typing `/difficulty up` into a real PTY saved while stopped. After `s` started
  mining, typed `/difficulty up`, `/difficulty down` and `/difficulty reset`
  each updated the displayed multiplier and produced accepted blocks.
- Wrong-network and missing-cookie configurations were rejected.
- Core proposal mode validated a constructed block with a witness transaction
  without changing the active tip, checking proof of work, or starting the miner.
- `workers 1`, `workers up`, `workers down`, and `workers` work while stopped.
  A worker change while mining restarted the service and resumed with two workers.
- Offline readiness cases reject known header lag, missing public peers, payout
  script disagreement, compact-target disagreement, and rejected proposals.
- Concurrent starts attached to one supervisor; repeated start did not duplicate it.
- Pause stopped the hash counter; resume continued work; restart replaced the service.
- Malformed local control input did not interrupt mining.
- Stop completed and a subsequent start succeeded; the final state was stopped.
- The actual Terminal UI rendered, `s` started mining, a scripted stop completed,
  and `q` closed the view. Tests use `stop --no-summary` to avoid putting test
  reports on the user's Desktop. The `t` shortcut itself is covered by offline tests.

The evidence file, `validation/regtest.json`, records version, block/transaction
hashes, check descriptions and source digests. Packaging verifies those digests
before setting `core_regtest_validated` in BUILD-INFO.json. That run covered its
then-current Ember and difficulty-control code; it used only disposable mining services.
The existing Bitcoin-Qt installation and normal node data were not used or modified.
The previous and duplicate difficulty reports remain available in Git history.
The run includes the dynamic-rods primality implementation in THESIS2.

## Ellipse and dynamic rods

The 18 additional tests compare dynamically extended rods with an independent sieve
through 20,000, reproduce the 65-prime window, enforce its exclusive square boundary,
check CRT extension and all 35 qualifying primes, and verify the actual traversal uses
the new primality routine. Exact ellipse identities, inverse reconstruction, eccentricity
intervals and Fermat budgets are checked, including algebra on integers whose product
exceeds 8192 bits. Those large example factors are not claimed prime.

The code-to-theorem mapping and a correction to the source's informal shape explanation
are in `MATH-IMPLEMENTATION.md`. Earlier logs and exact `/math` output remain in
Git history. A later independent check rebuilt the completed
Aristotle task's EllipseSearch, DynamicRods and CorePrimes plus 10 local dependencies.
The axiom union for their 83 theorem roots contains only `propext`,
`Classical.choice`, and `Quot.sound`. This checks the Lean sources, not the Python
implementation formally. See `validation/aristotle-current/latest-validation.json`
and `ARISTOTLE-MONITOR.md`. An earlier clean package build passed 94 tests,
including the added core-prime and monitor checks.

## Performance observations

Short comparable single-worker tests, including candidate generation and hashing,
measured THESIS2 at 3.94 MH/s before optimization and 17.65 MH/s afterward (about
4.5 times faster). The linear control measured 16.06 and 18.18 MH/s respectively;
normal measurement variability is present. These are not sustained thermal results.

The new real-engine benchmark includes the scheduler, THESIS2 generation, and
default diagnostics (sampling eligible nonces every 64):

| Workers | MH/s | Duration |
| --- | ---: | ---: |
| 1 | 9.10 | 3 seconds |
| 2 | 17.53 | 3 seconds |
| 4 | 18.94 | 3 seconds |
| 8 | 17.81 | 3 seconds |

The two-worker default is retained. Diagnostic output is written into a temporary
directory; these benchmarks send no network requests or shares. Keep-awake and
idle policies are disabled during measurement. The earlier performance receipt
remains available in Git history.

```
./bin/btc-miner benchmark --strategy thesis2 --seconds 3 --sweep
```

## Limits

Regtest acceptance is actual Bitcoin Core validation on a private test chain. It
does not establish mainnet success, real pool compatibility, profitability, or a
THESIS2 advantage over ordinary SHA256d search. That historical run included no full-domain 2^32 enumeration,
Lean proof, prolonged thermal run, forced-crash watchdog scenario, or system
sleep/wake test was performed. Opening the application never starts mining.
