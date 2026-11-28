#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout}
project=$(cd "$project" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
modules=(Graph189R1Metric Graph189WedgeOrder Graph189RetainedWidth Graph189HighThirdLayer Graph189ColumnCancel Graph189RootWidth)
cp "$src"/Graph189{R1Metric,WedgeOrder,RetainedWidth,HighThirdLayer,RootWidth}.lean "$out"/
cp "$src"/../lowblock/Graph189ColumnCancel.lean "$out"/
if [[ ${1:-} == --replay-test ]]; then
  cp "$src"/Graph189{WedgeCorollary,RootedOreCount,RootedPath,RootedTrace,WidthInterval,WidthReplayBridge}.lean "$out"/
  cp "$src"/../order/Graph189{DegreeCeiling,MaximumDegree}.lean "$out"/
  cp "$src"/../global/arity/final/Graph189{FiniteDomain,ScalarReplay}.lean "$out"/
  modules+=(Graph189WedgeCorollary Graph189RootedOreCount Graph189RootedPath Graph189RootedTrace Graph189DegreeCeiling Graph189MaximumDegree Graph189WidthInterval Graph189FiniteDomain Graph189ScalarReplay Graph189WidthReplayBridge)
fi
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
