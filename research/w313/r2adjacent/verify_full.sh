#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "$0")" && pwd)
ramsey=$(cd "$work/.." && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
export LEAN_BIN=${LEAN_BIN:-lean}
"$LEAN_BIN" --version
compile() {
    local path=$1
    local name
    name=$(basename "$path" .lean)
    printf 'Checking %s\n' "$path"
    "$LEAN_BIN" -o "$build/$name.olean" "$path"
}
cd "$ramsey"
compile Green160NearWitness.lean
for name in Green130WindowCore Green130Window64 Green130R2Bridge; do
    compile "window141/$name.lean"
done
for name in Green137WindowCore Green137Window27 Green150WindowCore Green150Window14 GreenR2Adjacent; do
    compile "r2adjacent/$name.lean"
done
"$work/edge154/verify.sh" "$build"
compile r2adjacent/GreenR2AdjacentFull.lean
