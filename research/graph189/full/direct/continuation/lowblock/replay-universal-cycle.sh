#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned checkout with built mathlib}
project=$(cd "$project" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cp "$src/Graph189UniversalCycle.lean" "$build/"
cd "$project"
lake env bash -c '
set -euo pipefail
cd "$1"
lean -j1 -DwarningAsError=true -o Graph189UniversalCycle.olean Graph189UniversalCycle.lean
' _ "$build"
