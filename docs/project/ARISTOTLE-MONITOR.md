# Aristotle monitoring and miner integration

Selected task: https://aristotle.harmonic.fun/projects/9b854e2d-2ae1-4d55-9b53-bf308b5e3648?task=acfd50e8-1951-4593-986d-30a11b056e92

The task completed on 29 September 2026. The requested local monitor checks it
every hour through the originally scheduled 24-hour deadline. Exact end time, last successful check, errors,
validation status and implementation review status are in
`validation/aristotle-current/status.json`. A detached local process runs it
independently of this chat and keeps the Mac awake while monitoring. Internet
access and the logged-in Mac are required. It does not survive logout or reboot.
The LaunchAgent attempt was blocked by macOS Desktop privacy permissions and
was unloaded; the monitor uses the same process-launch approach as the existing
Aristotle exporter, with the current session's access to the requested files.

The process has a fixed end time. To stop early, inspect the PID in `status.json`,
confirm it is `monitor_aristotle_math.py`, then send that process SIGTERM.
An active audit has its separate PID and process start identity recorded in
`active-validation.json`.
To restart after logout or reboot using the saved deadline:

```sh
python3 -B scripts/monitor_aristotle_math.py --watch-until "2026-09-30T21:19:08.875982+00:00"
```

Checks use Aristotle's read-only task and file endpoints. On a changed completed
revision, the monitor captures exact sources and hashes, compiles the selected
relevant modules and all their local dependencies against the installed pinned
Lean 4.28.0/Mathlib environment, collects transitive theorem axioms, and runs
the miner regression suite. Only `propext`, `Classical.choice`, and `Quot.sound`
are accepted. A failed check is recorded and retried. It never sends prompts or
changes the remote Aristotle project.

Each cycle also checks all pages of the project's run list. The newest run's ID,
status and progress are recorded separately from the original task's validation.
A newer run is marked awaiting completion. Once complete, the monitor downloads
that run's versions of the eight selected modules and their local import closure,
rebuilds them, audits their theorem axioms, and runs the miner regression suite.
Each run has a separate report in `task-validations/`; the original validated
report is preserved. This automatic check covers EllipseSearch, DynamicRods, CorePrimes, RodCircles,
RodScaling, ShellEnrichment, TowerCollapse and BaseDensity, plus local imports.
Identical previously validated build artifacts may be reused when the source,
local dependency closure, Lean version and pinned dependency manifest match. A passed new run remains pending
implementation review; it never inherits the original run's integration status.

`latest-validation.json` identifies the exact checked revision; detailed build
logs, source copies, theorem names, axiom union and regression output are under
`revisions/`. These are checks of the selected modules, not of every theorem in
the entire Aristotle project. The pinned Mathlib dependency cache is reused.
The local monitor requires `.test-tools` and the earlier math-audit snapshot;
these large development dependencies are not bundled in the portable miner.

New source hashes require implementation review: passing a Lean proof alone
does not automatically change executable miner code. The monitor also checks
the reviewed Python file hashes. It records pending review if either changes;
it does not send chat notifications or generate new Python implementations.
New formulas needing code changes remain pending implementation review.

## How the math is used

`btcminer/pqmath.py` supplies the dynamic prime rods used by
`thesis2.qualifying_primes()` and the actual THESIS2 traversal. The exact ellipse
and Fermat routines remain available as described in `MATH-IMPLEMENTATION.md`.

`btcminer/coreprimes.py` adds selected executable counterparts of the completed
task's `CorePrimes.lean`. The dashboard `/math` and this command use them:

```sh
./bin/btc-miner math inspect --strategy thesis2
```

The `core_primes` result includes:

| Lean result | Python use |
| --- | --- |
| `core_chi`, `core_mod_twelve` | Classify 11, 19, 71, 97, 109 on square and hexagonal grids. |
| `r2_scale`, `rHex_scale` | Exact prime-power circle-count multipliers; enforce a coprime positive base. |
| `coreScale_richness`, `core_pow_scale` | Distinguish scaling squared radii (9×/27×) from scaling coordinates (25×/125×). |
| `coreRods`, `coreScale_eq` | Exact CRT round trips on the five square rods with capacity 24615334061206009. |
| `scale_bijective_iff` | Reject normalization when the scale loses information modulo the rods. |
| `pair_97_109` | Compute the 16 square-grid and 24 hexagonal-grid points. |
| `core_exponent`, `korselt_fails_on_square` | Report exponent 30240 and expose the square-rod restriction. |

For the existing 144000 clock, only 11, 19 and 97 of the five satisfy
`(p-1) divides 144000`; 71 and 109 do not. All five remain available for the
rod/geometry calculations. Complete nonce coverage and native SHA256d acceptance
remain the mining criteria. These results do not demonstrate a hashing advantage.

Python ports are tested against independent coordinate counts, CRT reconstruction,
boundary cases and actual math-report integration. They are not Lean-extracted or
formally verified Python. Source files and the reviewed source-to-implementation
hash mapping are in `reference/aristotle-core-primes/`. The previous source copies
and earlier validation evidence are preserved.

## September 29 rods, flowers and towers update

Task `81f0a318-7967-4c28-80cd-dd06e558ae4d` adds five research modules.
`btcminer/rodmath.py` ports selected executable results; `/math` and
`math inspect --strategy thesis2` include them under `rods_flowers_towers`.
Prime rod circles count modular solutions, unlike the integer lattice circles
in `core_primes`. Hexagonal rod circles use x²+xy+y²=1. CRT multiplication
requires distinct prime rods; ramified primes are excluded from the formula.

The shell recurrence computes signed integer coordinates in 2, 3 and 4
dimensions. Independent enumeration tests its geometric meaning: the Lean
source itself checks recurrence values without proving that interpretation.
Tower reductions check every modular period hypothesis before reducing an
exponent. The 7^(11^c) example has 72 distinct residues on the core rods.

`split_with` ports the existing OrderSplit scan used by BaseDensity. It
requires a complete prime-factor list for its supplied exponent. Its probability
guarantee additionally assumes n=p*q for distinct primes and an exponent
multiple of lcm(p-1,q-1). For a uniform base among all pq residues, the lower
bound is (p-1)(q-1)/(2pq), not one-half; the 11*19 example gives 90/209.
This does not supply the unknown factors or a suitable exponent for arbitrary n.

These are tested Python counterparts, not formally extracted implementations.
They run in math diagnostics; dynamic rods continue to supply the actual
nonce traversal. No new result supports skipping nonces, changing Bitcoin's
proof-of-work check, or claiming a hash-rate improvement. General prime-power
rod-circle lifting and the general four-square formula are not claimed from
finite checked examples. Reviewed source and implementation hashes are recorded
in `reference/aristotle-rods-towers/reviewed-sources.json`. This records the
implementation review; the monitor separately requires a successful audit of
all eight selected modules before reporting the new task as integrated.

The first expanded local proof audit exceeded its ten-minute module limit.
A retry explicitly uses one Lean worker and a thirty-minute per-module limit
to reduce memory pressure. Status remains pending during that retry; the
watcher runs independently of the active audit, with the original
September 30 deadline preserved.

## Hourly checks and automatic application

The watcher checks the project every 3600 seconds. Lean runs in a separate
process, so a long proof audit does not block discovery of later tasks. A PID
and process-start identity prevent duplicate audit workers; checks and outcomes
are saved in `status.json`, `checks.jsonl`, and per-task validation reports.

The user authorized application while mining. When a reviewed completed task
has a successful expanded Lean/axiom audit and its reviewed source/Python
hashes match, `scripts/apply_math_update.py` runs fresh miner regression tests.
It then reloads the implementation through a controlled stop/start only if
the same session is actively MINING. A stopped, paused, replaced, or already
updated miner is left alone. Startup snapshots record the loaded math hashes.
This is local application, not publication to a remote repository.

The reload drains pending submissions and checks the final saved session.
Any accepted block prevents restarting, including one found during the drain.
The updater preserves the saved network, payout and stop-after-block settings.
A source mismatch or failed test prevents application; failed startup verification
leaves the miner stopped. Application results are saved in `deployment.json`.

This automation can validate new proof revisions and apply an existing reviewed
implementation. It cannot translate arbitrary new Lean research into a new
mining algorithm. Such research stays pending until implemented and reviewed.

A newer in-progress research task does not block an already reviewed update.
The watcher separately checks the reviewed task's remote revision and local
proof report, queues any missing audit, and applies it once all checks pass.
The running process must report the new math hashes after restart; otherwise
the updater stops it and records the failure in `deployment.json`.

Heavy Lean audits are deferred while the miner supervisor is running, including
startup, reconnect and pause. If mining starts during an audit, the audit worker
terminates its Lean subprocess within the next polling interval (two seconds).
Lean also has a 2048 MB allocation limit. This prioritizes Core RPC responsiveness
on this 8 GB Mac; deferred or resource-limited proofs stay pending. Hourly remote
checks and application of already validated, reviewed updates remain enabled.
