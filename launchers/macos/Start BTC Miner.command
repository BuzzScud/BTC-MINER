#!/bin/bash
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
"$ROOT/bin/btc-miner" ui
RESULT=$?
if [ "$RESULT" -ne 0 ]; then
    echo
    read -r -p "Press Enter to close this window. "
fi
exit "$RESULT"
