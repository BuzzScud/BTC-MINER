# Optional desktop launchers

The root `setup.sh`, `setup.ps1`, `bin/btc-miner`, and `btc-miner.cmd` remain the
primary setup and command-line entry points. These optional launchers must stay
inside the repository so they can find its source and private environment.

On macOS, open **macos/BTC Miner.app** or **macos/Start BTC Miner.command** to open
the terminal dashboard. **macos/install.command** runs setup. If macOS blocks a
launcher, right-click it and choose Open.

For a PowerShell launcher, run `./launchers/windows/btc-miner.ps1 ui` from the
repository root. The root `btc-miner.cmd` also works in PowerShell and CMD.

Opening the dashboard does not start mining. Closing it leaves an explicitly
started miner running; use the stop command to stop mining.
