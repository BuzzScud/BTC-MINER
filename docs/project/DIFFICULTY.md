# Regtest difficulty controls — 1.2.4

Use a private Bitcoin Core regtest node to test finding blocks at different rates.
The existing `/network` menu supports mainnet, testnet4, legacy testnet3 and regtest.
Select `/network regtest`, configure that node and a regtest payout address with
`/setup`, then check `/doctor --connect`. A network switch leaves mining stopped.

| Dashboard command | Result |
| --- | --- |
| `/difficulty` | Show the active and saved multiplier, limits and available controls |
| `/difficulty up` | Double the multiplier, capped at 9,007,199,254,740,991 |
| `/difficulty down` | Halve it, rounding down, with a minimum of 1 |
| `/difficulty reset` | Restore multiplier 1, the normal regtest target |
| `/difficulty 256` | Set an exact integer multiplier |

From a shell, use `./bin/btc-miner difficulty up` (without the slash).
The Ember header shows **Test difficulty ×N** on Core regtest. The JSON status
includes `regtest_difficulty_multiplier`; the human-readable status also shows it.

While stopped, these commands save the setting without starting mining. While
running, a changed value validates configuration, stops the old session, saves,
and starts a new session. Session counters reset, with the same restart semantics
as worker controls; a manual pause is cleared. A no-op at either limit does not
restart. If stopping fails, the saved setting is unchanged. If saving or starting
fails, the command reports the error; inspect status before starting again.

The value is saved in `machine.local.json` as `regtest_difficulty_multiplier`,
defaults to 1 for existing installations, and is dormant outside Core regtest.
The upper bound keeps integers exact in JSON clients. Target arithmetic uses
arbitrary-precision integers; the 32-bit nonce space does not cap this multiplier.
For example, `/difficulty 100000000000` sets a local multiplier of one hundred billion.
Returning to regtest restores the saved multiplier. Mutating `/difficulty`
commands are rejected for public networks and pool connections. Merely showing
`/difficulty` is always allowed.

## What changes

The miner requires `hash <= floor(network_target / multiplier)` before submitting
a regtest block. Header nBits, the network target, block serialization, payout and
nonce traversal stay unchanged. All strategies use the same target check. Blocks
that meet this stricter local threshold also meet Core's normal proof-of-work
requirement. Multiplier 1 is the easiest valid setting; fractional values are not
accepted. This is additional local work, not a change to the chain's consensus
difficulty. At ×256, finding a solution takes roughly 256 times as many hashes
on average as at ×1, with randomness in individual results.

Higher settings reduce the expected solution rate; they do not increase hash
throughput. Public testnet/mainnet targets remain controlled by the network.
Pools still use their assigned share target; the existing `pool_difficulty`
setting only sends a suggestion that the pool may accept or ignore.

## Verification

The 115-test offline suite covers target isolation, unchanged consensus fields,
limits, invalid inputs, no-op/stopped/running controls, failure paths, CLI routing,
and Ember display/routing. The isolated Bitcoin Core 31.1 integration accepted a
block at ×256 with its stricter hash independently checked using hashlib. Live
changes to ×256, ×512, ×256 and ×1 each restarted the miner and produced accepted
blocks. All node/service lifecycle tests ran in a disposable project and data
directory with public peers disabled.

The follow-up audit also typed `/difficulty up`, `/difficulty down` and
`/difficulty reset` into a real terminal connected to that private node, checked
the displayed multiplier and accepted blocks after each restart, exercised
simultaneous difficulty commands, and verified no-op/invalid commands preserve the
running process. A regtest → testnet4 → regtest round trip restored the configured
private node and multiplier without starting mining.

The retained evidence is `validation/regtest.json`; the duplicate report and
detailed follow-up logs remain available in Git history.
Reproduce with `python3 -B scripts/regtest.py`; supply `--bitcoind /path/to/bitcoind`
if needed. This creates and cleans up its own test node, not a persistent regtest
connection for the dashboard.
