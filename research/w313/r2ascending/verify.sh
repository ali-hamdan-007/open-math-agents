#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "$0")" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean_bin=${LEAN_BIN:-lean}
"$lean_bin" --version
(
    cd "$work/.."
    "$lean_bin" -o "$build/Green160NearWitness.olean" Green160NearWitness.lean
)
cd "$work"
for module in Green147WindowCore Green147Window52 GreenR2Premises GreenR2Ascending; do
    "$lean_bin" -o "$build/$module.olean" "$module.lean"
done
