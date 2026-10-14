#!/bin/bash
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGED="$(mktemp "$HERE/.abacus-build.XXXXXX")"
trap 'rm -f "$STAGED"' EXIT
cc -std=c11 -O2 -shared -fPIC -I "$HERE/latcalc/include" \
    "$HERE"/latcalc/src/*.c -lm -o "$STAGED"
if [ "$(uname)" = Darwin ]; then
    codesign --force --sign - "$STAGED"
    mv -f "$STAGED" "$HERE/libabacus.dylib"
else
    mv -f "$STAGED" "$HERE/libabacus.so"
fi
echo "Built shared coprime-rod abacus."
