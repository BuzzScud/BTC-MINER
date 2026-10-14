# BTC MINER

A terminal Bitcoin miner with THESIS2 field/flower traversal, exact coprime-rod
arithmetic, native SHA256d, verified pruning, and durable work distribution.
The public default matches the original flower traversal: step 7, prime 19.
The original mathematical sources and scoped Lean evidence are preserved.

## Terminal setup

Clone or download this repository. Setup checks dependencies, asks before
installing them, builds the native libraries, and runs hash and proof checks.
It never starts mining or installs a startup service.

**macOS (Apple Silicon or Intel) and Linux (64-bit):**

```sh
git clone --branch stable https://github.com/BuzzScud/BTC-MINER.git
cd BTC-MINER
sh setup.sh
./bin/btc-miner ui
```

**Windows x64 (PowerShell / Windows Terminal):**

```powershell
git clone --branch stable https://github.com/BuzzScud/BTC-MINER.git
cd BTC-MINER
powershell -NoProfile -ExecutionPolicy Bypass -File .\setup.ps1
.\btc-miner.cmd ui
```

The one-process PowerShell execution-policy option does not change your machine's
saved policy. Alternatively, run `py -3 scripts/setup_terminal.py`, then
`.venv\Scripts\python.exe -m btcminer ui`.

Python 3.9+ is required. Setup offers platform compiler installation when needed:
Apple Command Line Tools, Linux build tools, or Visual Studio 2022 Build Tools
with Clang on Windows. Dependencies install only in `.venv`; compiler packages
may require OS permission. If installation is interrupted, rerun setup.
Windows ARM and 32-bit platforms are not release targets.

## First run

The wizard asks for solo Bitcoin Core or a Stratum pool, network, payout/worker
information, and resource limits. It validates inputs before saving. Mining starts
only when you press **s** in the dashboard or explicitly run `start`.

- **Solo:** run your own fully synchronized Bitcoin Core with RPC enabled. The
  wizard detects the usual OS data directory; select another path if necessary.
  Prefer Core's local cookie authentication. The miner does not create a wallet,
  download the blockchain, change Core settings, or request a wallet seed.
  Remote Core connections require `rpc_tls=on`, a trusted HTTPS reverse proxy,
  and an explicit RPC username or cookie path. Core itself serves HTTP; a secure
  tunnel ending on loopback is the alternative. RPC redirects are refused and
  automatic local cookie discovery is never used for a remote host.
- **Pool:** enter the pool's Bitcoin Stratum V1 endpoint and its required worker
  name/password. `stratum+ssl://` enables TLS; `stratum+tcp://` is plaintext.
  An optional backup endpoint supports failover. Stratum V2-only pools need a
  compatible gateway. Check your pool's minimum share difficulty for CPU mining.
- **Resources:** choose worker, CPU and RAM limits. The controller uses sampled
  guards, not hard quotas. Linux/Windows low-memory pressure is based on available
  memory; thermal instrumentation is not available on every OS. Linux automatic
  desktop-idle pause is unavailable and the wizard disables that setting there.

No personal wallet, account, token, provider endpoint or machine settings ship
with the repository. Pool passwords entered in the wizard stay in ignored,
private local settings. RPC/provider secrets can be supplied through environment
variables; avoid placing secrets directly in shell command history.

## Everyday commands

Use `./bin/btc-miner` on macOS/Linux, `.\btc-miner.cmd` on Windows, or the virtual
environment's Python with `-m btcminer`. Commands are the same:

```text
setup                       configure this installation while stopped
ui                          open the Copper dashboard
self-test --require-native  check native hashing against reference calculations
doctor --connect            inspect setup; check Core without starting mining
start                       explicitly start mining
status                      inspect the current session
pause                       pause hashing
resume                      resume hashing
stop                        stop and retain a session summary
math                        inspect the mathematical implementation
```

Dashboard keys: **s** start, **t** stop, **p** pause/resume, **q** close the view.
Closing the view leaves a running miner running. Configuration changes to a running
miner can restart it; stop first when preparing a different connection.

For guided calculator login, run `./bin/btc-miner provider login` (Windows:
`.\btc-miner.cmd provider login`). Enter your provider endpoint, existing account
and password at the hidden prompt. Login verifies the account, saves only the
endpoint/account and enable setting, and opens the dashboard. Mining still needs
an explicit start. The password stays in memory and is inherited by this
dashboard's miner processes; no password or session token is saved to disk.
Use `provider login` again after reopening the app. Account registration and
password recovery remain on the provider's website. Stop the miner before
changing accounts.

For automation, optional calculator integration uses your own `BTC_PROVIDER_URL`
and `BTC_PROVIDER_SESSION`; enable with `config set provider_enabled=on provider_user=YOUR_ACCOUNT`.
Use a dedicated provider token; closing a shared session can affect its other consumers.
Alternatively set BTC_PROVIDER_PASSWORD to let the runtime create its own session.
Remote calculator endpoints must use HTTPS; HTTP is accepted only on loopback
for a trusted local tunnel. It verifies sampled job math
and observes models; the native backend performs mining hashes. Unavailable
provider telemetry is not evidence of a failed arithmetic identity.
See [provider details](docs/PROVIDER-API.txt) and
[work distribution](docs/FRACTAL-DISTRIBUTION.txt).
The external Algorithm Observatory opened by `/hub` is a separate optional project;
it is not required for mining or bundled in this release.

## Send and receive updates

This follows the XMR miner's main/follower model. `stable` is the release channel;
a push to `main` alone does not update followers. Every Git installation defaults
to follower. It checks for a release when the dashboard opens, or with `update`.
Checks use a 15-second Git network timeout; offline, the installed version opens.
A new release takes longer because it builds and validates before switching.
Nothing polls or interrupts a miner while its dashboard stays open.

**On your publishing machine, once:**

```sh
./bin/btc-miner role main
```

Review changes, refresh the public manifest, and commit only the reviewed public
files. Then publish with:

```sh
./bin/btc-miner release
```

The command requires [Gitleaks](https://github.com/gitleaks/gitleaks), or
`release --gitleaks PATH`. It checks the exact source inventory, preserved math,
proof evidence, and secrets; pushes the committed revision to `main`; waits for
all platform CI checks; then publishes `main` and `stable` in an atomic Git push.
It never stages or commits arbitrary local files. If CI fails, `stable` stays put.
Git authentication is needed only on the publisher. `--yes` skips its final prompt.

**On other machines:** reopen the dashboard, or run:

```sh
./bin/btc-miner update --check
./bin/btc-miner update
```

Use `.\btc-miner.cmd` instead of `./bin/btc-miner` on Windows. A follower builds
and tests the candidate first, then stops only its own miner and switches to the
release. **It stays stopped until the user starts it.** Settings, credentials,
wallets and logs remain local. Tracked edits are saved in Git stash and local
commits in a `backup/` branch. Untracked-file collisions postpone the update;
nothing runs `git clean` or a forced checkout. Follower pushes are disabled locally.
Tracked edits are backed up and restored to the release even when the commit ID
is already current; use the main role for the checkout where you develop changes.
`role main` restores publishing capability; changing roles never changes math.

When dependencies change, dashboard launch postpones the update. Manual `update`
asks before installing the pinned packages into a separate environment, keeping
the old environment for rollback. Missing system compiler tools require setup's
separate approval. A failed switch restores the prior source, binaries and runtime;
`update --rollback` recovers an interrupted switch. Recovery refuses to overwrite
concurrent user edits. Details and retained backups are in ignored `.updates/`.

An installation from before this updater needs a one-time `git pull --ff-only`
and setup; resolve any Git conflicts first. ZIP-only copies need a Git clone to
follow releases. Publishing a release cannot directly change an offline machine
or a checkout that has not installed the updater. Existing open dashboards see
updates on their next launch.

## Mathematics and evidence

`src/` and `math-library/` are canonical sources; compatibility copies are included
so cloning on Windows needs no symlink privileges. Native C arithmetic and Lean
statements are preserved. Platform changes cover OS services, build/loading,
configuration and terminal setup. See [preservation checks](docs/PUBLIC-RELEASE.md).

```sh
.venv/bin/python scripts/check_math_integrity.py
.venv/bin/python scripts/verify_proof_evidence.py
.venv/bin/python -B -m unittest discover -s tests
```

On Windows use `.venv\Scripts\python.exe` in those commands.
The capsule verifier checks retained evidence for 299 audited roots / 123 named
statements. It does not recompile Lean or prove the complete miner correct.
Additional scoped contract sources are included. Metadata with personal paths
was anonymized with a recorded dependency-hash mapping; Lean sources and compiled
proof objects were preserved. Historical validation is not silently extended to
this portability release.

CPU mining can validate the implementation, but at mainnet difficulty a CPU has
an extremely small chance of finding a solo block. Geometric traversal and the
proofs do not establish a SHA256d search advantage. Hashing a candidate is distinct
from having a block accepted by Bitcoin Core.

## Development

See [public release design and checks](docs/PUBLIC-RELEASE.md),
[security and publication](SECURITY.md), and [source provenance](SOURCE-NOTES.md).
CI builds native libraries and runs tests on macOS, Linux, and Windows.
`docs/HISTORICAL-README.md` preserves the earlier research narrative; paths to
unbundled private experiments are historical references, not setup prerequisites.
License: GPL-3.0; see [LICENSE](LICENSE).
