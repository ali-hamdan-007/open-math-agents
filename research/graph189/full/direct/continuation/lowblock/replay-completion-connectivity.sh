#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with built mathlib}
project=$(cd "$project" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cp "$src/../root"/Graph189{CrossPort,CrossOrder,SeparatorCover,HighPredecessor}.lean "$out/"
cp "$src/../verify"/Graph189{R1Metric,WedgeOrder}.lean "$out/"
cp "$src/../order"/Graph189{CutSides,MinimumCut,MinimumCutOrder}.lean "$out/"
cp "$src"/Graph189{UniversalCycle,CompletionConnectivity,RemovableCompletion}.lean "$out/"
modules=(Graph189SeparatorCover Graph189CrossPort Graph189CrossOrder Graph189HighPredecessor
  Graph189R1Metric Graph189CutSides Graph189MinimumCut Graph189WedgeOrder Graph189MinimumCutOrder
  Graph189UniversalCycle Graph189CompletionConnectivity Graph189RemovableCompletion)
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  shift
  for module in "$@"; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' _ "$out" "${modules[@]}"
