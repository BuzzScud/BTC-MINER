# BTC MINER

A terminal Bitcoin miner with native SHA256d, THESIS2 traversal, resource controls,
and authenticated work distribution. Runs on macOS, Linux, and Windows x64.

## Get started

**macOS / Linux**

```sh
git clone --branch stable https://github.com/BuzzScud/BTC-MINER.git
cd BTC-MINER
sh setup.sh
./bin/btc-miner ui
```

**Windows — PowerShell**

```powershell
git clone --branch stable https://github.com/BuzzScud/BTC-MINER.git
cd BTC-MINER
powershell -NoProfile -ExecutionPolicy Bypass -File .\setup.ps1
.\btc-miner.cmd ui
```

Setup checks dependencies and asks before installing them. The wizard configures
your own Bitcoin Core node or pool, payout/worker information, and resource limits.
No personal accounts, wallets, or credentials ship with the repository.

**Mining starts only when you press `s` or run `start`.** In the dashboard,
`p` pauses/resumes, `t` stops, and `q` closes the view. Closing the view leaves a
running miner running.

## Documentation

- [User guide](docs/usage.md) — requirements, connections, commands, and updates
- [Documentation index](docs/README.md) — development, mathematics, and evidence
- [Optional desktop launchers](launchers/README.md)
- [Security and credentials](SECURITY.md)

`stable` is the release channel. Development changes on `main` reach followers
only after release checks pass and a release is published.

## Source

`src/` and `math-library/` contain canonical sources. `btcminer/` and `native/`
provide compatibility paths. Build tools live in `scripts/`, tests in `tests/`,
and supporting material in `docs/`, `research/`, `reference/`, and `validation/`.

CPU mining has an extremely small chance of finding a solo mainnet block.
The geometric traversal and retained proofs do not establish a SHA256d search
advantage or prove the complete miner correct.

Licensed under [GPL-3.0](LICENSE).
