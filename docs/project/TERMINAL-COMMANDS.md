# Testnet4 first: Terminal commands for this Mac

## Full-screen mining loop

Inside the miner UI, type `loop` and press Enter (or `/loop`). The four steps fill
one screen in a clockwise loop. Narrow windows stack them in execution order.

- `1`–`4` or Tab selects a step; Enter or `e` opens its editor.
- Up/Down selects a field; Enter edits it; Ctrl+U clears text; Enter keeps the draft.
- Ctrl+S or the **Save & apply** row saves. Invalid values stay in the editor with
  an error. Mining-setting changes restart a running miner. Labels save separately.
- Esc cancels a field, then an editor; Esc from the loop returns to the dashboard.
- `s` starts, `t` stops, `p` pauses/resumes, `f` freezes observations, `+`/`-` adjusts
  workers. These shortcuts do not run while typing in a field. `q` closes the view.
- `/setup` edits the connection and credentials; `/network` switches networks;
  `/config` shows all settings. `/dashboard` returns to the original dashboard.

Opening the loop does not start mining. Displayed samples describe completed work;
they do not measure time spent in each native stage. Reopen an older terminal view
to load this UI code. Closing the view leaves a running miner running.

Prepared September 29, 2026 for BTC Miner 1.2.2. The miner is stopped, configured
for THESIS2, one worker, and a ten-minute session. Keyboard activity will not pause
this initial test. Public-network mining has not started. The dedicated testnet4
node configuration exists; its wallet will be created by the commands below.

The existing Bitcoin-Qt 28.1 mainnet node is separate. Its last read-only check
reported chain `main`, blocks=headers=969192, and initialblockdownload=false.
The testnet4 node uses the locally installed Bitcoin Core 31.1 command-line binaries.

## 1. Enter the project and check the miner

```zsh
cd "/source/user/Desktop/MINER STUFF/BTC MINER"
./bin/btc-miner --version
./bin/btc-miner self-test --require-native
./bin/btc-miner status --json
```

Expect version 1.2.2, `ok: true`, and `STOPPED`.

## 2. Start the dedicated testnet4 node

This starts a public testnet4 connection and synchronization; it does not start mining.
Run these commands in the same Terminal tab so the directory variable remains set.

```zsh
BTC_TESTNET_DIR="$HOME/Library/Application Support/Bitcoin-Miner-Testnet4"
./.test-tools/bitcoin-31.1/bin/bitcoind -testnet4 -datadir="$BTC_TESTNET_DIR" -daemonwait
./.test-tools/bitcoin-31.1/bin/bitcoin-cli -testnet4 -datadir="$BTC_TESTNET_DIR" getblockchaininfo
./.test-tools/bitcoin-31.1/bin/bitcoin-cli -testnet4 -datadir="$BTC_TESTNET_DIR" getnetworkinfo
```

Wait for `chain: testnet4`, `initialblockdownload: false`, blocks equal to known
headers, `networkactive: true`, and at least one connection. Repeat the two read-only
commands to check progress. The miner's connected doctor checks these conditions too.
Synchronization needs network downloads; pruning limits retained block files, not
total download traffic or all disk use. Node settings use a 256 MiB database cache,
two script-verification threads, a 64 MiB mempool limit, and a 2000 MiB pruning target.

If the node is already running, skip its start command. A data-directory lock error
is a reason to inspect the running node, not to delete its lock or data.

## 3. Create the dedicated test wallet and receiving address

Create the wallet once. Its name and directory are dedicated to testnet4. The following
creates a local test wallet without a passphrase; do not reuse it as a mainnet wallet.

```zsh
./.test-tools/bitcoin-31.1/bin/bitcoin-cli -testnet4 -datadir="$BTC_TESTNET_DIR" -named createwallet wallet_name=btc-miner-testnet4 load_on_startup=true
BTC_TEST_ADDRESS="$(./.test-tools/bitcoin-31.1/bin/bitcoin-cli -testnet4 -datadir="$BTC_TESTNET_DIR" -rpcwallet=btc-miner-testnet4 getnewaddress "BTC Miner test" bech32)"
./bin/btc-miner config set "address=$BTC_TEST_ADDRESS"
```

The generated address begins with `tb1`. It is a public receiving address, not a
private key. If the wallet already exists, inspect `listwallets` and, if necessary,
use `loadwallet btc-miner-testnet4`; do not recreate or delete it.

## 4. Validate the connection and open the CLI

```zsh
./bin/btc-miner doctor --connect && ./bin/btc-miner ui
```

The doctor must report `core_ready: true` and `proposal.valid: true`. It checks
network/sync/peers, the payout script, the compact target, and Core validation of a
constructed block. Proposal validation deliberately excludes proof of work; it does
not broadcast a block or start hashing. The `&&` opens the dashboard only if it passes.
These checks do not promise that a valid proof of work will be found during the test.

## 5. Controls inside the dashboard

| What to type | Effect |
|---|---|
| `s` | Start mining the configured testnet4 node |
| `t` | Stop mining and save a Desktop session summary |
| `/workers` | Show worker count and options |
| `/workers up` | Increase by one, up to the Mac's logical CPU count |
| `/workers down` | Decrease by one, with a minimum of one |
| `/workers 2` | Set exactly two workers |
| `/network` | Open network menu; arrows or 1–4 choose, Enter selects and tests, Esc cancels |
| `/network mainnet` | Save current connection settings, select mainnet, leave mining stopped |
| `/network testnet4` | Restore testnet4 connection settings and leave mining stopped |
| `/network regtest` | Select a private regtest connection; configure its Core node and payout before starting |
| `/difficulty` | Show the local regtest multiplier and available controls |
| `/difficulty up` / `/difficulty down` | Double / halve local regtest work; restart if mining |
| `/difficulty reset` / `/difficulty 256` | Restore ×1 / set an exact multiplier; Core regtest only |
| `/usage` | Inspect hash counts, connection, and accepted blocks |
| `/logs` | Inspect events and rejection reasons |
| `p` | Manually pause/resume |
| `/doctor --connect` | Repeat the candidate readiness check |
| `q` or Ctrl+C | Close the view; a running miner continues |

Press Enter after slash commands. `s` and `t` are single-key controls. A worker
change while mining restarts the service with the new setting and resets the
ten-minute session timer. To finish, use `t` before `q`. `run_seconds=600` includes
pauses and connection waits; it is not a promise of ten full minutes of hashing.

Network switches remember each network's payout address and connection settings
locally. An unconfigured network begins with Core defaults and an empty address.
Review `/config` and run `/doctor --connect` before starting. Selecting the current
network changes nothing. `testnet` means legacy testnet3; use `testnet4` for this trial.
The same selector works from Terminal: `./bin/btc-miner network mainnet --check`.

From a second Terminal tab, using the same project directory:

```zsh
./bin/btc-miner status --json
./bin/btc-miner workers 2
./bin/btc-miner logs --lines 100
./bin/btc-miner stop
```

For a longer test, stop first, then use `./bin/btc-miner config set run_seconds=1800`.
The value `0` means no session time limit. Reopening the dashboard never starts mining.

## 6. Stop the dedicated node when finished

```zsh
./bin/btc-miner stop
./.test-tools/bitcoin-31.1/bin/bitcoin-cli -testnet4 -datadir="$BTC_TESTNET_DIR" stop
```

This stops the dedicated testnet4 node. It does not stop the separate mainnet GUI node.

## Mainnet selection and connection

Mainnet needs a mainnet receiving address controlled by you and authentication for
the existing node. This Mac's existing Core configuration uses credentials;
the miner now reads them directly from the local `bitcoin.conf` when its default
cookie is absent. Network profiles keep testnet4 addresses and settings separate.

The eventual sequence, with your real values supplied interactively, is:

```zsh
./bin/btc-miner stop
read "BTC_MAIN_ADDRESS?Your mainnet receiving address: "
./bin/btc-miner network mainnet --check
./bin/btc-miner config set "address=$BTC_MAIN_ADDRESS"
./bin/btc-miner doctor --connect && ./bin/btc-miner ui
```

Then use `s` and `t`. The connection check does not start mining and can pass before
a payout address has been set; the full doctor checks the payout and candidate block.
Testnet4 coins have no BTC monetary value; mainnet uses real
BTC. A short CPU solo-mining test may finish without finding a block on either network.

## Implementation choices, broadest to simplest

1. **Comprehensive:** testnet4 template/proposal checks, a bounded CPU test, lifecycle
   and stale-work review, sustained resource measurements, then mainnet preflight;
   subsequently evaluate the historical native worker pool and optional Metal backend.
2. **Recommended first run:** the prepared one-worker, ten-minute testnet4 setup,
   explicit `s`/`t`, `/workers` controls, and review of the saved session evidence.
3. **Simplest verification:** offline self-test and private regtest only. These already
   pass, but they do not establish public-network operation.

The new geometry research remains outside the production nonce path. Any proposed
factor or nonce filter needs a completeness argument and an equal-work experiment
before it can replace the current full-domain THESIS2 traversal.

Core's documented [synchronization fields](https://bitcoincore.org/en/doc/31.0.0/rpc/blockchain/getblockchaininfo/)
and [proposal-mode implementation](https://github.com/bitcoin/bitcoin/blob/v31.1/src/rpc/mining.cpp)
support the distinction between a ready node, a valid candidate, and a solved block.

## Formula inventory and code consumers

From this project folder:

```sh
python3 -B -m btcminer abacus formulas
python3 -B -m btcminer abacus formulas --query fractal
python3 -B -m btcminer abacus formulas --query 109
```

These read the reviewed 1,302-record snapshot and its typed code-consumer map.
They do not contact the provider or start mining. Source-only relationships and
remaining proof-to-implementation obligations remain explicit in the output.
# Provider API commands — 2026-10-12

`/provider capabilities` reads public discovery. `/provider refresh` retrieves
current account-visible formulas and saves `logs/provider/latest.json`.
Use `/provider formulas --query rod`,
`/provider calculate --expression '11*15*17'`,
`/provider watch --seconds 10`, or `/provider check`.
Shell equivalent: `./bin/btc-miner provider ...`.
See [provider authentication and scope](../PROVIDER-API.txt).
