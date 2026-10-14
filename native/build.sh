#!/bin/bash
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGED="$(mktemp "$HERE/.hasher-build.XXXXXX")"
trap 'rm -f "$STAGED"' EXIT
if [ "$(uname)" = Darwin ]; then
    if [ "$(uname -m)" = arm64 ]; then
        clang -O3 -arch arm64 -march=armv8-a+crypto -mmacosx-version-min=13.0 -shared -fPIC \
            -o "$STAGED" "$HERE/hasher_fast.c"
    else
        clang -O3 -shared -fPIC -o "$STAGED" "$HERE/hasher_fast.c"
    fi
    codesign --force --sign - "$STAGED"
    mv -f "$STAGED" "$HERE/libhasher_fast.dylib"
else
    cc -O3 -shared -fPIC -o "$STAGED" "$HERE/hasher_fast.c"
    mv -f "$STAGED" "$HERE/libhasher_fast.so"
fi
echo "Built native SHA256d hasher."
bash "$HERE/build_rodsieve.sh"
bash "$HERE/build_abacus.sh"
