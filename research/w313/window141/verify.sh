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
for module in Green141WindowCore Green141Window43 Green141Window73     Green130WindowCore Green130Window64 Green130R2Bridge; do
    "$lean_bin" -o "$build/$module.olean" "$module.lean"
done
if [[ ${1:-} == --old ]]; then
    cd ../extension160
    "$lean_bin" Green160FourRed.lean
fi
