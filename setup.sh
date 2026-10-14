#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo "Install Python 3.9+ from https://www.python.org/downloads/ and rerun setup."
  exit 1
fi
exec python3 scripts/setup_terminal.py "$@"
