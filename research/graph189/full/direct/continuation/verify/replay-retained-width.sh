#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with built mathlib}
project=$(cd "$project" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cp "$src"/Graph189{WedgeOrder,RetainedWidth}.lean "$build"/
cd "$project"
lake env bash -c '
set -euo pipefail
export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
cd "$1"
lean -j1 -DwarningAsError=true -o Graph189WedgeOrder.olean Graph189WedgeOrder.lean
lean -j1 -DwarningAsError=true -o Graph189RetainedWidth.olean Graph189RetainedWidth.lean
printf "%s\n" "import Graph189RetainedWidth" "#print axioms Graph189RetainedWidth.geodesic_degree_width" | lean -j1 -DwarningAsError=true --stdin
' _ "$build"
