#!/bin/bash
# Familiar XMR Miner command entry point.
exec "$(cd "$(dirname "$0")" && pwd)/btc-miner" "$@"
