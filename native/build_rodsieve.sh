#!/bin/bash
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGED="$(mktemp "$HERE/.rodsieve-build.XXXXXX")"
trap 'rm -f "$STAGED"' EXIT
cc -O2 -shared -fPIC -I "$HERE/latcalc/include" \
    "$HERE/latcalc/src/bigint.c" "$HERE/latcalc/src/rns.c" \
    "$HERE/latcalc/src/common.c" "$HERE/latcalc/src/rodsieve.c" -o "$STAGED"
if [ "$(uname)" = Darwin ]; then
    codesign --force --sign - "$STAGED"
    mv -f "$STAGED" "$HERE/librodsieve.dylib"
else
    mv -f "$STAGED" "$HERE/librodsieve.so"
fi
echo "Built guarded recurrence verifier."
