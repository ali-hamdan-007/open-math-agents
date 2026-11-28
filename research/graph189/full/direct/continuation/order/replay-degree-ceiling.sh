#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with built mathlib}
project=$(cd "$project" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
cp "$source_dir"/Graph189{DegreeCeiling,MaximumDegree}.lean "$build_dir/"
cd "$project"
lake env bash -c '
set -euo pipefail
export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
cd "$1"
lean -j1 -DwarningAsError=true -o Graph189DegreeCeiling.olean Graph189DegreeCeiling.lean
lean -j1 -DwarningAsError=true -o Graph189MaximumDegree.olean Graph189MaximumDegree.lean
printf "%s\n" "import Graph189MaximumDegree" "#print axioms Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree" | lean -j1 -DwarningAsError=true --stdin
' _ "$build_dir"
