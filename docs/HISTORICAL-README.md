# BTC MINER

Local Bitcoin miner for the **2023 M2 Mac mini, 8 GB RAM, macOS Sequoia 15.1.1**.
This folder is the install. Copy it to the M2 and keep its contents together.

## Thesis API integration — 2026-10-12

With `provider_enabled=on`, each mining session automatically starts the provider
connection, refreshes its formula catalogue, receives compressed model events and
checks sampled flower/rod job arithmetic. Copper shows API, stream and job-math
status. The provider process stops with the miner; network delays do not block
hashing. This installation has the setting enabled. Portable defaults remain off.

Use `/provider refresh` to retrieve current API capabilities and account-visible
formulas, `/provider calculate --expression '11*15*17'` to evaluate an expression,
and `/provider watch --seconds 10` to observe model events. `/provider check`
checks ten calculator results and 15 synthetic codec cases against the service.
The client supports TCMP HTTP/WebSocket negotiation, bounded decoding and raw
request fallback when encoding expands data. REST uses the standard library;
WebSocket observation additionally requires `aiohttp`. Existing macOS Keychain
credentials are reused without exposing them in snapshots.
See [commands, authentication and measurement scope](docs/PROVIDER-API.txt).

## Copper Console — 2026-10-10

Open **BTC Miner.app** or **Start BTC Miner.command** for the Copper terminal UI.
Reopen an older terminal view to load the new design; closing a view leaves mining
running. The wide layout has rate/hash/block metrics, an embedded mining-loop
panel, session details, an Observatory shortcut, and an activity ledger. Smaller
windows keep essential results and controls; **e** switches loop/events.

- **f** freezes/resumes displayed observations only. Live lifecycle state and
  stop/pause notices remain visible; **p** still pauses the actual miner.
- Type **loop** or **/loop** to replace the dashboard with the full-screen cycle:
  **Get job → Prepare candidates → Hash nonces → Submit result → Get job**.
  Use **1–4 / Tab** to select a step and **Enter / e** to edit its label and settings.
  **Enter** edits or commits a field; **Ctrl+U** clears it; **Ctrl+S** saves and applies.
  Changed mining settings use the existing configuration command and restart a
  running miner. Labels save separately in `logs/loop-view.json` without restarting.
  **Esc** cancels a field/editor first, then returns to the dashboard; **/dashboard**
  also returns. Use **/setup** for connection credentials and **/network** to switch networks.
- **/hub** (also **/HUB**) starts or reuses the local Algorithm Observatory and
  opens its live-miner section in the browser. No synthetic study starts.
- **s** starts, **t** stops, and **q / Ctrl+C** closes only the terminal view.

Loop values come from current status and bounded samples in `model-events.jsonl`.
They identify completed batches and diagnostic SHA256d replays, not every native
hash or instruction. Missing, disabled and stale samples remain explicit. There
is no percentage toward finding a block. Viewing the loop does not change mining work; controls and Save & apply are explicit actions.
Status is polled serially every 0.5 seconds after each reply; memory collection is
separate. Changed terminal rows are painted at up to 10 Hz, with immediate input
redraws. Split arrow/UTF-8 input is buffered and bracketed paste cannot trigger
mining shortcuts. Stop can interrupt a read-only diagnostic; lifecycle operations
retain ordered stop handling.

The Hub is a separate workspace dependency. It discovers the existing sibling
`bitcoin-algorithm-observatory-2026-10-07` folder, or an `observatory` folder inside
this install. Use `/hub --path "/path/to/observatory"` or `BTC_OBSERVATORY_ROOT`
after moving it. Its Python environment requires `aiohttp`. The launcher checks
server/root identity, handles occupied ports, and exposes only loopback. Browser
failure shows a local URL. Closing the browser leaves both mining and the local
viewer server running. The miner ZIP does not bundle the Observatory research tree.

Code lives in `src/ui/tui.py` (interaction), `copper.py` (dashboard),
`loop_view.py` (full-screen cycle and editor), `ui_support.py`
(input/observations/painting), and `hub.py` (browser launcher).
`btcminer/` retains import aliases. Loop terminal checks use
`scripts/check_loop_terminal.py`; fixture previews and receipts live in
`validation/fullscreen-loop-20261011/`.
Fixture verification: `scripts/check_copper_terminal.py` and
`scripts/check_copper_hub.py`; results are in `validation/copper/`.
Preview PNGs there are rendered from actual ANSI output with invented fixture
data, not a live mining measurement. The Ember section below describes the prior UI.

## Miner geometry transport

THESIS2 now has a durable tile/cell/label partition scheduler for local and
authenticated remote nodes. `BTC_NODE_ID` identifies each peer; `cluster worker`
joins the coordinator and exchanges modeled duplex buffer frames. Calculator
model previews are independently checked, with an explicit local fallback for
the provider's missing shared-buffer service. See
[distribution, recovery, setup and proof scope](docs/FRACTAL-DISTRIBUTION.txt).
The scheduler is enabled for normal THESIS2 runs; its network listener remains
off until configured. No production mining is started by installation.

The exact scale-graph runtime now supports two THESIS2 candidate orders:
`thesis2_order=field` preserves the existing order; `thesis2_order=flower` uses
two-digit flower addresses. Both use independent rod arithmetic and projection
in native candidate generation, with an exact per-job scale trace and full nonce
coverage. `/math` includes the general flower boundary and finite-dynamics results.
See [the scale graph, formulas and controls](docs/SCALE-GRAPH-TRAVERSAL.txt).
This is a different mathematical traversal, with descriptor encoding secondary
to the frame/tower semantics. The source references and runtime proof scope are
recorded in `research/scale-graph-runtime.json`.

The pruning worker now accepts versioned orbit, bounded residue and Q-route
references from `math-library/python/geometry_codec.py`. Negotiated NG2 adds
shortest-arc rod deltas, hex-shell charts, root-relative offsets, predictive/raw
selection and compressed adaptive rod-count streams in `geometry_predictive.py`. Shared-frame fingerprints,
canonical bit packing and exact local replay bind reconstruction. Q routes retain
both the clock class and within-class index. Raw JSON and packed nonce bytes remain
available; the sender selects only a smaller complete message.

Run `/abacus compression` to inspect synthetic round trips and measured message
sizes for all applicable modes, plus the one-time capability exchange cost.
The worker must advertise NG2 before the sender uses it. See [the format and scope](docs/GEOMETRY-CODEC.txt) and
[mathematical arguments and gates](research/geometry-codec-contract.json).
This changes private candidate IPC; it grants no nonce-exclusion authority and
is not a general fractal file codec or a new formal implementation proof.

## Historical proof blockers repaired — 2026-10-07

The local repaired `RodCircles`, `RodScaling`, and `TowerCollapse` modules now
pass fresh Lean and Lake builds. Both assumption audits agree on 299 theorem
roots across the six-module local closure. All 45 original theorem statements
and hypotheses are preserved; the larger scaling count is proved in 19 blocks.
The gate rejects false arithmetic, admitted proofs, and custom assumptions.

See the [portable proof report](research/proof-evidence/report.html) and
[project contracts](project/MASTER_PLAN.md). Run
`python3 -B scripts/verify_proof_evidence.py` to verify current mathematical
sources, retained objects and both assumption inventories without external paths.
The release gate additionally validates the typed executable catalogue and registry.

Fresh Lean replay requires the full research workspace and pinned dependencies:
`make -C validation/miner-proof-repair-20261007 check`. The research-only workflow
and historical reports are retained in that workspace; they are not prerequisites
for the portable evidence check.
The repaired copies and source patches are maintained in that review workspace;
historical provider sources and failed attempts remain preserved. This closes
the three named proof blockers. The other five historical top-level modules
were outside this targeted replay, and these proofs establish no SHA-256 mining
advantage or complete refinement of the miner runtime.

## Fresh validation — 2026-10-07

The October 7 baseline passed all 213 tests without skips in its recorded environment, an isolated native rebuild,
Bitcoin Core regtest acceptance and lifecycle checks, 2,101 miner Lean roots and
22 shared-abacus roots. Q→k separately passed 3,466 native comparisons, eight
injected-fault checks and 12 freshly compiled Lean contract roots. The Q→k proof
replay uses one Lean worker and a 4096 MiB memory bound; the earlier smaller-memory
failure is retained as incomplete evidence.

That recorded provider run failed eight of 83 required formula
checks; current provider status requires a fresh run, and 12 additional precision/policy observations are not correctness passes.
The local calculator passes all 83 required cases. The research runner now
supports `--live --login` with credentials kept in memory. These results do not
establish complete implementation refinement or mainnet/pool qualification.
See the [fresh HTML report](validation/retry-20261007/report.html) for proof scope,
the broader proof retry, API follow-up and source-bound evidence.

## Strict math audit — 2026-10-06

The current source rejects invalid compact targets and inconsistent Core template
targets, preserves the exact floor when a pool target becomes zero, validates
nonce and coinbase boundaries, and checks every proposed nonce exclusion with an
independent SHA256d calculation. Audit cleanup preserves an initially stopped miner.

The audit and follow-up reviews passed 213 distinct tests across the standard and optional Z3 environments,
an isolated Bitcoin Core regtest lifecycle, 2,101 Lean theorem/certificate axiom
checks, and a separate rebuild and axiom check of 22 shared-abacus theorem roots.
These checks cover explicit mathematical contracts and finite implementation
outputs; they do not establish a formal refinement of all Python/C code or finish
the broader archived Aristotle audit. See
[the detailed audit](validation/strict-audit-2026-10-06/report.html).

The second review also checks exact hash-target equality, uint32 scan wraparound,
and the combined 100-byte coinbase script limit. A zero hash now reports
`best_difficulty: null` with `best_difficulty_unbounded: true`; subsequent finite
shares preserve that result. Ordinary difficulty statistics remain binary64
approximations computed from independently checked solution hashes.

The third review corrects wrapped-nonce hit accounting in priority statistics and
extends update fingerprints to all runtime Python files and bundled native
libraries. A new exact Lean contract bounds the smoothed priority score by one
when its target and observed hit counts are valid.

## Version 1.3.0 — Integrated abacus and Testnet4 validation

The live task path now uses bounded adaptive bit-and-carry pruning and an
experimental probability/arithmetic priority order. Every arithmetic rejection
has a fallback; unknown solver results retain all unresolved candidates.
Only the full Bitcoin SHA256d model can exclude a Bitcoin nonce. The original
coprime-to-30, coprime-to-210 and clock-product filters are ordering rules.
Priority has no demonstrated predictive advantage. Solver and bookkeeping costs
are additional work and can outweigh the concrete hashes they avoid.
The symbolic filter evaluates full SHA constraints. Every proposed removal also
requires an independent verification hash. Worker scan counts exclude these
additional hashes, which appear as `verification_hashes` in pruning state.
Removed candidates therefore do not represent an established saving in total hashes.

The resident model includes all three Q dictionaries (703 / 4,371 / 15,051
products), reversible k/index coordinates, actual bit packing on supported
worker requests, and dynamically sized signed CRT arithmetic. Unknown Q values
remain raw. The recurrence sieve and guarded native verifier run on their exact
recurrence certificates; those certificates do not exclude Bitcoin nonces.

Commands inside the miner:

```
/abacus
/abacus compression
/abacus precision --precision-bits 65536
/abacus recurrence
/abacus toy --width 64 --rounds 64 --scale 33264000 --difficulty 16
/pruning
/network testnet4 --check
```

Toy checks use the same adaptive engine with a separate model and independently
scan the declared domain after freezing the retained set. They cannot replace
Bitcoin consensus hashing. SHA256 still uses its standard 32-bit words and
256-bit outputs; larger CRT inputs do not change the Bitcoin algorithm.

`scripts/test_testnet4.py` verifies public Testnet4 historical winners and real
targets, then tests a fresh proposal and bounded live mining when Core is fully
synced. Historical replay uses supplied known nonces and is not a new-block
discovery benchmark. A duplicate submission is not block acceptance. Reports
are in `validation/testnet4`; isolated lifecycle regressions are separately
labelled regtest. Mainnet connection settings remain saved in their profile.

Lean/Lake checks cover the stated coverage lemmas, recurrence soundness and
finite large-integer certificates. They do not formally verify the complete
Python/C implementation or the SMT solver. The broader Aristotle project audit
remains separately tracked; passing these checks does not complete it.

## Ember terminal interface

The dashboard now uses the selected Ember design: warm charcoal and copper,
a full-width network/status header, an event ledger, and grouped session,
results, engine/strategy and connection details in the right rail. The prompt
and familiar keys stay at the bottom. Open **BTC Miner.app** or
**Start BTC Miner.command** to use it; an already-open view needs reopening.

All existing commands, setup steps and mining controls retain their behavior.
The layout adapts to small windows and keeps detailed math under `/math`.
See [EMBER-IMPLEMENTATION.md](project/EMBER-IMPLEMENTATION.md) for implementation and checks.

## Version 1.2.4 — Regtest difficulty controls

Use `/difficulty up`, `/difficulty down`, `/difficulty reset`, or `/difficulty 256`
on a configured Bitcoin Core regtest connection. Ember shows the current multiplier.
Changes while stopped only save; changes while mining restart the session and reset
its counters. Multiplier 1 is the easiest valid setting. Public-network and pool
targets are unchanged. See [DIFFICULTY.md](project/DIFFICULTY.md) for setup, limits and checks.

### Version 1.2.3 — Exact ellipse math and dynamic prime rods

Dynamic prime rods now perform the primality checks used to select THESIS2's
qualifying primes. The exact pq ellipse, eccentricity intervals, bounded Fermat
search and CRT rod extension are implemented in `btcminer/pqmath.py` and shown by
`/math`. See [MATH-IMPLEMENTATION.md](project/MATH-IMPLEMENTATION.md) for the theorem mapping,
runtime integration and validation. The bundled Lean sources are preserved unchanged;
the Python port is tested, not formally verified. These factor-search identities do
not establish a Bitcoin nonce filter or a SHA256 shortcut.

### Network selection (added in 1.2.2)

`/network` opens a menu with Mainnet, Testnet4, Testnet3 and Regtest. Use arrow keys
or 1–4, then Enter to select and test the Core connection; Esc cancels.
The result confirms the node's actual chain, sync state and peer count.
`/network mainnet` and `/network testnet4` also switch networks and leave mining
stopped. The footer shows the selected network.
Connection settings and payout addresses are remembered separately in
`network-profiles.local.json`, which stays local and is excluded from packaging.
The first visit to a network uses Core defaults and needs that network's payout
address and authentication. Returning to testnet4 restores its dedicated data folder.
Review `/config`, run `/doctor --connect`, then use `s` when ready. Selecting the
already-active network preserves settings; selecting it in the menu still tests
the connection. `testnet` explicitly means legacy testnet3; `regtest` is also
supported. Terminal syntax: `./bin/btc-miner network mainnet --check`.

`/workers` shows the worker count; `/workers up`, `/workers down`, and `/workers 2`
change it. A change while mining performs a controlled restart. `doctor --connect`
now checks public-network peer connectivity, synchronization, payout-script agreement,
template target agreement, and Core's validation of a constructed block proposal.
Proposal validation excludes proof of work and does not broadcast a block.
See `TERMINAL-COMMANDS.md` for the staged testnet4 procedure on this Mac.

THESIS2 remains the default. Its native batch generator preserves the original
nonce order, passes packed buffers directly to the hasher, and batches diagnostic
writes. The Terminal uses **s to start and t to stop**. An unconfigured start opens
setup; a stop pressed during another command is queued instead of ignored.

The current build passes 213 offline regression tests and an isolated Bitcoin Core
31.1 regtest, including acceptance of a witness block and a block at local difficulty
×256, live difficulty changes, concurrent start/attach, pause/resume, restart, stop,
and the Terminal start control. The Ember checks cover resizing and exit cleanup.
See `VALIDATION.md` and `validation/regtest.json` for scope and evidence.
Mainnet and live pool operation, sleep/wake, and sustained thermal behavior have
not been validated. No network mining starts automatically.

```bash
./bin/btc-miner self-test --require-native
python3 -B -m unittest discover -s tests -v
python3 -B scripts/build.py
python3 -B scripts/regtest.py --bitcoind /path/to/bitcoind
./bin/btc-miner benchmark --strategy thesis2 --seconds 3 --sweep
```

The build command compiles and tests in a clean staging folder, then writes a ZIP
under `dist/`. It excludes local configuration and session logs and includes a
fresh checksum manifest. Building requires a C compiler and macOS signing tools;
running the included native binary does not. Signing is ad-hoc, not notarized.
The regtest script starts and stops a separate node with temporary data and no
public peers. It does not use the existing Bitcoin-Qt application's data folder.
Bitcoin Core test binaries are not redistributed in the miner archive.

The terminal uses Ember's ledger + right rail and warm colors, retaining the command
palette, start/stop keys, worker controls, and Desktop session summaries. The engine supports
Bitcoin Core solo mining and **Bitcoin Stratum V1** pools, with the original BTC thesis
math preserved alongside linear and hybrid search. **Version 1.1 defaults to the new
`thesis2` strategy**, using the supplied `thesis2-math-in-pictures.html` as its math reference.
Open **THESIS2 Implementation Report.html** in this folder for the completion report.

## Start on your M2

1. Copy this entire folder to the M2. Any writable folder is fine.
2. Open **BTC Miner.app** or **Start BTC Miner.command**. If macOS blocks it, right-click
   the launcher and choose Open. `install.command` can also prepare permissions and the native library.
3. Type **`/setup`**. Choose `core` or `pool` and enter your connection details.
4. Press **`s`** to start. Press **`t`** to stop and save a Desktop summary.

**Python 3.9 or newer is required.** No pip packages, browser, Node, database, Docker,
or Flask are required. A signed arm64 SHA-256 library is already included, so Xcode is
not needed on the M2 for normal use. The launcher prefers Homebrew Python when present,
otherwise `python3` on PATH. `BTC_PYTHON=/absolute/path/to/python3` overrides that choice.

Opening the app does **not** start mining. There is no login service. **`q` or Ctrl+C
closes the terminal view and leaves an explicitly started miner running.** Reopen the
app to reconnect to it. Stop with `t` or `./bin/btc-miner stop`.

The default pauses hashing while the keyboard or mouse is active and resumes after
120 seconds idle, like XMR Miner. The dashboard shows `PAUSED` during this time.
Use **`/pause off`** to mine while using the Mac. `p` is a separate manual pause/resume.

## Connection setup

### Bitcoin Core

Bitcoin Core must be installed separately, fully synced, and running with RPC enabled
(`server=1`). The miner does not install, start, stop, or modify your Bitcoin node.

`/setup` asks for a payout address, RPC host, port, data folder and optional cookie path.
The default cookie location is `~/Library/Application Support/Bitcoin/.cookie` on mainnet.
Set `rpc_datadir` to the **base data folder**; the correct network subfolder is appended.
An explicit `rpc_cookie` overrides discovery. Mainnet, testnet3, testnet4 and regtest are
supported. Signet mining is not advertised because it requires additional block signing.

For username/password RPC, set `rpc_user` and export `BTC_RPC_PASSWORD` in the Terminal
that starts the miner. `rpc_password_env` selects a different environment variable.
For a loopback node with no cookie and no explicit authentication override, the
miner can use `rpcuser`/`rpcpassword` from the local data folder's `bitcoin.conf`
when its RPC port matches. The credentials remain in Core's file and are never
copied into miner settings. Config includes/custom config paths require explicit
authentication settings.
Current public releases allow HTTP only on loopback. Remote Core RPC requires
rpc_tls=on, a trusted HTTPS proxy, and explicit authentication; alternatively use
a secure tunnel ending on loopback. Automatic cookie discovery remains local
only, and redirects are refused. Do not expose Core RPC to the public internet.

```bash
./bin/btc-miner config set connection=core network=mainnet 'address=YOUR_BTC_ADDRESS'
./bin/btc-miner config set 'rpc_datadir=/Volumes/Bitcoin/BitcoinData'
./bin/btc-miner doctor --connect
./bin/btc-miner start
```

### Pool

Enter a **Bitcoin SHA256d Stratum V1** endpoint supplied by your pool, including its port:

```text
stratum+ssl://POOL_HOST:PORT    TLS with certificate verification
stratum+tcp://POOL_HOST:PORT    Plain Stratum TCP
```

Set `pool_user` to the pool's account/worker or address/worker format. If `pool_user`
is empty, the miner uses `address.worker`. Pool passwords commonly use `x`; follow your
pool's instructions. `BTC_POOL_PASSWORD` overrides the saved pool password.

```bash
./bin/btc-miner config set connection=pool 'pool=stratum+ssl://YOUR_POOL:PORT'
./bin/btc-miner config set 'pool_user=YOUR_ACCOUNT.YOUR_WORKER' pool_password=x
./bin/btc-miner config set 'backup=stratum+ssl://YOUR_BACKUP:PORT'
./bin/btc-miner start
```

No default pool or payout address is supplied. A pool must accept CPU-scale workers and
offer suitable share difficulty. Setting `pool_difficulty` sends a suggestion; the server
decides whether to honor it. Pool support is V1, not Stratum V2. Mining uses the pool's
assigned target and extranonce; it does not alter a pool's payout coinbase or require wallet keys.

Accepted pool shares are not accepted Bitcoin blocks. The display keeps shares, Core
accepted blocks, network-target candidates, rejected solutions, and unknown submission
outcomes separate. A submission whose response is lost is not blindly resubmitted.

## Terminal controls

| Control | Action |
|---|---|
| `s` / `/start` | Start, or attach if already running |
| `t` / `/stop` | Stop this project's miner; save Desktop summary |
| `q`, Ctrl+C, `/quit` | Close the view; miner keeps running |
| `p` | Toggle manual pause |
| `+`, `−` | Adjust workers; presses gather for 1.5 seconds before applying |
| `/` | Command palette; arrows select, Enter runs, Tab completes |
| `/usage` | Session statistics |
| `/config` | All settings |
| `/set KEY=value` | Save setting and restart if running |
| `/unset KEY` | Restore default setting |
| `/perf eco`, `/perf auto`, `/perf max`, `/perf 4`, `/perf 50%` | Worker count |
| `/workers`, `/workers up`, `/workers down`, `/workers 2` | Show, increase, decrease, or set workers; restart if running |
| `/pause on`, `/pause off`, `/pause 300` | Keyboard/mouse idle policy |
| `/resume` | Clear manual pause; idle policy still applies |
| `/strategy thesis2`, `thesis`, `linear`, `hybrid` | Select search mode |
| `/connection core`, `pool` | Select saved connection |
| `/logs`, `/err` | Events / service output |
| `/restart` | Restart without a Desktop summary |
| `/math` | Inspect active math; `/math --strategy thesis` shows retained legacy math |
| `/probe`, `/probe --compare`, `/probe --z0` | SUPT reports |
| `/backtest --blocks 100` | Historical THESIS2 traversal rank, or legacy membership, through Core |
| `/bench --sweep` | Offline native throughput sweep; requires stopped miner |
| `/bench --strategy thesis2 --sweep` | Offline scheduler + traversal + configured diagnostics |
| `/doctor`, `/doctor --connect` | Local diagnostics; add `--connect` for Core candidate validation without mining |
| Esc | Close card/palette or cancel setup |
| Arrows / PageUp / PageDown | Scroll a card |

The right rail folds away below 100 terminal columns or 24 rows. On a larger terminal it shows
hashrate windows, share counts, worker settings, strategy, connection and session.
There is no remote fleet control, hub, schedule or automatic update system in this local edition.

Every command is also scriptable:

```bash
./bin/btc-miner --help
./bin/btc-miner status --json
./bin/btc-miner start --connection core --strategy thesis2 --workers 2
./bin/btc-miner start --dry-run
./bin/btc-miner stop
./bin/btc-miner math inspect --height 900000 --bits 17034219
./bin/btc-miner probe --window 71 --source stream_b
./bin/btc-miner benchmark --seconds 3 --sweep
./bin/btc-miner logs --lines 100
```

`./bin/minerctl.sh` is a compatibility entry point for the same commands. CLI output uses
JSON except the human-readable `status`, logs, help and setup. Errors return nonzero.

## M2 defaults and settings

Settings live in `machine.local.json`, created by setup or the first configuration change.
It is written atomically with owner-only permissions and excluded from git.

| Setting | Default | Meaning |
|---|---|---|
| `workers` | `2` | Native hashing threads; `eco` 1, `auto` 2, `max` all logical CPUs |
| `cpu_duty` | `100` | Per-worker duty cycle; reduce to soften load further |
| `yield_cpu` | `true` | Lower process priority; no sudo required |
| `pause_on_active` | `120` | Idle seconds before hashing; `0` disables |
| `keep_awake` | `true` | Prevent idle sleep only while this session runs |
| `strategy` | `thesis2` | `thesis2`, `thesis`, `linear`, `hybrid` |
| `thesis2_step` | `7` | Step coprime to 360; visits every field exponent |
| `thesis2_prime` | `19` | A prime p >= 7 for which p − 1 divides 144000 |
| `partition` | `quadrant` | Four logical quadrants, eight logical chunks, or original ordered list |
| `batch_size` | `16384` | Bounded scan size for responsiveness |
| `single_nonce_only` | `false` | First THESIS2 traversal nonce, or legacy base/recovery set |
| `phase3_nonces` | `65536` | Linear candidates after thesis in hybrid mode |
| `entropy_min`, `entropy_max` | `0.18`, `0.45` | Original thesis bounds |
| `native_hasher` | `true` | ARM SHA-256 engine, Python fallback if unavailable |
| `native_nonce`, `native_candidates`, `recovery` | `false` | Optional original C math; absent from source backup |
| `round_restart_seconds` | `600` | End a header round after this duration; `0` disables |
| `max_rounds` | `0` | Stop after this many header rounds; `0` unlimited |
| `run_seconds` | `0` | Session time limit including pauses; `0` unlimited |
| `stop_after_block` | `false` | Stop after a Core-accepted block |
| `supt_log`, `nonce_log` | `true` | Original math diagnostics |
| `supt_sample_every` | `64` | Log scanned nonces divisible by this value |

Logical strategy partitions do not force four/eight physical workers. The two-worker
default schedules all logical partitions. Percentage worker settings choose a fraction
of logical CPUs; they are not an exact overall system CPU cap. `cpu_duty` throttles each
worker. The SHA-256 engine does not allocate RandomX's multi-gigabyte dataset.

For a limited session:

```bash
./bin/btc-miner config set run_seconds=600 pause_on_active=0
./bin/btc-miner start
```

Reset those limits to `0` for unlimited sessions. Runtime changes cause a controlled
restart. Settings saved while stopped apply at the next start. Changing connection
type while mining stops the miner if the new connection still needs setup.

## Strategies and retained math

### THESIS2 (default)

The authoritative reference is bundled unchanged at `reference/thesis2-math-in-pictures.html`.
Its pure mathematics is ported in `btcminer/thesis2.py`: gcd/dial periods, arithmetic in
the 19² field with generator 1+3i, square and honeycomb norms, CRT for (8,9,5) and
(128,9,125), base-60 expansion, the qualifying-prime rule, signed multiplication,
base −1+i encoding, 4D neighbor/fill formulas, square roots of one modulo 144000, and
equal-area circle geometry. The source's three corrections are retained explicitly.

The HTML does not supply a Bitcoin nonce algorithm. The new `btc-traversal-v1` integration
uses its 360-element field cycle to order residues, CRT to reconstruct clock readings,
and a qualifying prime to traverse the 400 cells of a 144000-value tile. Header-derived
phases change the ordering for each job. Tiles partition the uint32 nonce domain, and
out-of-range entries in the final partial tile are skipped. Only one tile's uint32
offsets (576000 bytes) is stored, plus a bounded batch; there is no 2³²-element array.

The traversal is designed for full nonce coverage if allowed to finish. Job updates,
stops, pauses and configured round limits can end a round earlier. `single_nonce_only`
tries its first nonce only. Native SHA256d, pool targets and Bitcoin consensus validation
remain the acceptance mechanism. Qualifying primes select an ordering, not valid hashes.

The geometry, signs and Gaussian encoding are available through `/math` as mathematical
operations/diagnostics. They do not exclude candidate nonces or replace SHA-256. The old
entropy cuts, tetration recurrence, 500D candidate partition and recovery options do not
run inside `thesis2`; select `thesis` or `hybrid` to use those retained legacy controls.

`/backtest` in THESIS2 mode reports the traversal position of each published nonce on
its recorded block header, not a membership hit rate (the traversal covers the whole
domain). `/backtest --strategy thesis` retains the original candidate-membership view.
SUPT samples use a separate `thesis2` mode and appear in `/probe --compare`.

The original HTML's proof counts are source-reported. The new ellipse/rods Lean
sources are attached in `reference/aristotle-ellipse-rods/`.
Offline regression tests now cover tile permutations, sampled traversal ranks,
field coverage and selected math round trips. This Python port and traversal have
not been proof-checked; no mining-speedup claim is made.

### Retained legacy strategies

The pure Python algorithms from MINER-MAY-2026 retain their original numerical outputs:
clock prime seed, SFT fallback, crystalline boundaries, modular tetration recurrence,
entropy bounds, reassessment, 12 spheres, golden-ratio ordering, twin-prime/fractal/lunar
layers, polar lattice, 500-dimensional projection, and optional recovery interface.

* **Thesis:** scan the selected finite candidate list, then change the coinbase extranonce
  for a fresh header. Covering multiple regions does not mean every nonce was scanned.
* **Linear:** scan the full 32-bit nonce interval for that header, unless a new job, pause,
  stop or round limit interrupts it. Then obtain fresh work.
* **Hybrid:** thesis candidates followed by `phase3_nonces` linear candidates, excluding
  duplicates already searched by thesis for that header.
* **Single nonce:** only base/recovery guesses, then fresh header.

Native scans report the number actually attempted and resume after a found pool share.
Results are rehashed with Python SHA256d before submission. Pool jobs and Core templates
invalidate stale work. Each new header uses a unique extranonce within its connection.

THESIS2's optimized path keeps batches as uint32 buffers and fills them in C.
The Python generator remains the reference and fallback. The CRT reconstruction
is simplified using its exact modular identity; the traversal mapping version and
ordering are unchanged. Diagnostic sample values and counts are preserved.

The legacy `difficulty_bits` parameter is the compact target exponent, not actual hash
difficulty; its nonce leading-zero check is not a proof-of-work test. The modular
tetration recurrence is preserved for compatibility and is not general exact tetration.
All acceptance checks use the full Bitcoin hash target. These strategies are experiments;
the package does not claim an advantage over ordinary SHA-256 search or predictable income.

`backtest` reports whether published historical nonces occur in the original candidate
set. It is not a profitability model or proof that those candidates will succeed on a
different header. It uses block headers, so a pruned node can serve this analysis.
SUPT probes, Z0 views and mode comparisons are diagnostics. Their labels and reference
anchors are inherited research conventions, not mining-performance evidence.

Original optional `libalgorithms`/OBJECTIVE 28 sources are not included in the backup.
See `docs/OPTIONAL-BACKENDS.md`. The bundled ARM hashing library is separate and fully included.

## Sessions, reconnects and logs

Only one supervisor for this project folder can run. Controls use a local owner-only Unix
socket, with no web server or open control TCP port. Stop affects this BTC session only.

The pool reconnects every five seconds, uses the configured backup after five failed
attempts, and periodically probes the primary before switching back. Only configured
destinations are used. TLS certificates are verified. Node outages retry without changing
Bitcoin Core configuration. Core uses ordinary template polling at `template_refresh`
(15 seconds by default), avoiding abandoned long polls that can exhaust Core's RPC
workers on a quiet chain. Timestamp-only refreshes preserve current work; substantive
template changes retire it. An accepted block wakes polling immediately. External
changes are detected on the polling interval. Cookie credentials are reread for every
RPC request.

An unexpected engine exit triggers a 20-second wait and up to three restarts per hour.
A recorded stop never triggers that watchdog. Rebooting leaves mining stopped. Explicit
system sleep may still suspend the Mac; after wake, expired pool connections reconnect.

`logs/` contains:

* `events.jsonl` — bounded recent events; one rotated archive.
* `service.log` — supervisor/runtime output.
* `status.json`, `last-session.json` — current and last session.
* `reports.jsonl` — bounded session history.
* `nonces.jsonl` — legacy nonce details per height/difficulty.
* `thesis2-nonces.jsonl` — THESIS2 traversal version, phases and first nonces per header.
* `math/nonce_hash_stream.csv`, `block_cadence.csv`, `search_mode.jsonl` — bounded SUPT streams.

Stopping writes `BTC-miner-summary YYYY-MM-DD HH.MM.SS.txt` to the Desktop. A settings
restart keeps a local summary but does not create a Desktop file. Hash counters exclude
extra diagnostic rehashes used to record SUPT samples; throughput includes their wall time.

## Package contents and build status

```
BTC Miner.app/              Mac launcher (opens Terminal only)
Start BTC Miner.command     Portable terminal launcher
install.command            Optional local preparation; never starts mining
bin/                       CLI and familiar minerctl entry point
btcminer/                  Connections, engine, service, settings, terminal, diagnostics
btcminer/legacy/            Extracted BTC math and diagnostic modules
native/                    SHA-256 C source, signed arm64 library, rebuild script
optional/                  Instructions for missing original optional math libraries
reference/                 Unchanged authoritative THESIS2 HTML
THESIS2 Implementation Report.html   Completion report and source-to-code mapping
logs/                      Local runtime data
```

The arm64 library is compiled for macOS 13+ with explicit ARM crypto support and
ad-hoc signed. Version 1.2.0 includes offline regression tests, native/Python hash
comparisons, and actual Core regtest block acceptance and lifecycle checks.
Short full-engine benchmarks include strategy generation and configured diagnostics.
Mainnet, real pools, sleep/wake and long-duration thermal behavior remain unverified.

The original miner and XMR Miner folders were not modified. No original wallet address,
RPC credentials, XMR fleet tokens or local logs were copied into this package.

GPL-3.0; see LICENSE and SOURCE-NOTES.md.
# Lossless pruning (1.2.5)

`btc pruning` or `/pruning` in the dashboard shows the enabled filter and its actual counters. The default checks at most eight candidates on the first batch of each new job, with a 1,000 ms solver budget. `pruning_enabled`, `pruning_candidates` (1–64), and `pruning_budget_ms` (1–2,000) are normal configuration settings.

The production filter uses the complete Bitcoin SHA256d model and a necessary target-prefix condition. It removes a candidate only after an UNSAT result and an independent SHA256d check that the candidate exceeds the full target. A contradictory solver result retains the winner and increments `contradictions`. Missing solver support, timeouts, failed requests, and unprocessed candidates retain the original work. The helper process is reused and is closed when mining stops. On this installation it uses the existing `.test-tools/abacus-solver` environment; elsewhere it falls back to the miner's Python and retains candidates if Z3 is unavailable.

This deploys the conservative pruning mechanism studied in the toys, not their model-specific rejection lists or percentages. Symbolic full-round computation is additional work: current measurements do not establish a net computational advantage over native hashing. The native hasher and Core submission validation remain responsible for final solutions. Production source and next-start configuration are updated; opening the CLI does not start mining.

### Archived arithmetic calculations (1.5)

The shared native abacus now includes the full archived latcalc arithmetic
library. The miner retains local certificate, memory and lifetime guards.
`btc abacus calculate --claim '["eq",["mul","p","q"],209]' --variables
'{"p":11,"q":19}'` evaluates an integer claim in reusable rod slots.
Supported claim operators are `eq`, `le`, `dvd`, `and`, `or`, `not`; formulas
support `add`, `sub`, `mul`, and nonnegative integer `pow`. Divisibility is
rod-local only when the divisor divides the capacity; otherwise it reconstructs.
`btc abacus carries --width 32 --rounds 64` checks the SHA addition/carry
identities against this shared integer model, after calculating a trace.

Python research APIs in `btcminer.archive_math` provide supplied-k factor
recovery, conditional order splitting, persistent exact flower addresses,
native large-integer operations, and Ramanujan coefficients calculated on
resident rods. `btcminer.claim_calculus.count_polynomial_roots` multiplies
per-rod root counts over a complete CRT domain. These arithmetic calculations
are available in the miner; they do not authorize rejecting Bitcoin nonces.
Only the existing full-SHA necessary-condition filter can exclude live
candidates, retaining every unresolved candidate. Timing includes solver work.

`btcminer.archive_math.Clock24` keeps the twelve powers of the archived 4D clock
rotation loaded and applies the selected matrix to reusable rod columns. The
index is `depth % 12`, even for a large integer depth. This shortcut uses the
specific matrix's proven period; it does not imply periodic Bitcoin hashes.
`btc abacus theorems --theorem NAME --variables '{"n":19}'` instantiates a
published catalogue statement only when all its assumptions hold. Catalogue
publication waits for the proof export and bounded translation checks.

The resident clock model also keeps the complete 1,152-element F4 action as 24-byte permutations, plus all 1,152 flags as four-byte records (32,256 bytes of table payload, excluding Python object overhead and the four generator permutations). Construction checks the full orbit against an independently enumerated flag set. These geometry calculations do not authorize Bitcoin nonce exclusions.

`btcminer.archive_math.CircleModel` provides exact pair intersections and three-circle concurrence on the shared rod workspace. It requires a positive-definite integer form and nonnegative squared radii; coincident centres are classified separately, and collinear triples return an explicit non-applicable result. Tests include rational-coordinate oracles after 4,096-bit translations.
# Browse and audit the project

Run `./bin/btc-miner files` to generate and open `PROJECT-BROWSER.html`.
The browser has two independent panes: **Math library** (arithmetic code,
native math, math tests, proofs and reference material) and **Miner & supporting
files** (mining, hashing, networking, UI, configuration and tools). Every file
belongs to one side; mixed folders appear in both with their respective contents.
This is a navigation split: original paths and imports stay intact. Mathematical
consumers such as mining strategies remain on the miner side. Search and audit
filters apply to both panes, and each pane has its own folder navigation.
The landing view collapses top-level entries into four groups per side: code,
tests/tools, research or runs/releases, and documentation/configuration. Expand
a group to see its folders and files. Search and audit filters still cover the
entire indexed project; project totals are under an expandable summary.
Click folders to navigate, search any project path, inspect source previews,
or copy a file path/editor command. The browser includes hidden folders and
retained research dependencies; symbolic links are listed without traversal.
Local configuration and logs are listed without embedding their contents.

Run the command again after edits to see changes since the previous scan.
`./bin/btc-miner files --watch 30` regenerates every 30 seconds while that
Terminal command runs; Ctrl+C stops the watcher. The HTML page refreshes while
watching. Use `--no-open` for scripted generation or `--output /path/report.html`
for another destination. Existing unrelated HTML files are never overwritten.
In the miner terminal interface, `/files` opens the browser; run the continuous
watcher in a separate Terminal so it does not occupy the interface command queue.

Release comparisons use `.github/manifests/FILES.sha256.json`. Other change detection uses size
and modification time, supplemented by hashes for source previews. Matching
hashes are identity checks, not test or proof results. Run the relevant tests
after edits; the browser never changes source files or controls mining.
The generated HTML and `.project-browser-state.json` are local, regenerable
artifacts and are excluded from release packages.


## Simple source layout

The editable miner code is under `src/`, grouped by job: `main`, `config`, `pool`, `hash`, `workers`, `backends`, `stats`, `ui`, `tools`, and `legacy`. The exact mathematics is separate under `math-library/python` and `math-library/native/latcalc`. See [the folder map](docs/PROJECT-STRUCTURE.txt).

`./bin/btc-miner files` opens these two actual folders side by side. Existing `btcminer/` imports and native source paths remain compatibility links to the moved files. The build checks that every compatibility path matches its source. Existing terminal commands remain unchanged.

## Live modelling lab

For the separate Bitcoin network difficulty viewer, type `/target dif` in the
miner console (or run `python3 -B -m btcminer target dif`). This local recorded
HTML prototype has Network history, My miner and How it works tabs, with a
Core/public snapshot switch and all-history exploration. It has no automatic
refresh. See [the investigation and implementation plan](docs/NETWORK-DIFFICULTY.txt).

Run `python3 -m btcminer lab` (or `/lab` in the terminal UI) to open the local difficulty and scale experiment. Switch between a real SHA-256d header model and an isolated Bitcoin Core chain. Both field and flower orders are available together, with live target controls, rod-depth limits, sweeps and JSON export. See [the lab guide](docs/LIVE-MODELLING.txt).
