#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout}
project=$(cd "$project" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cp "$src"/Graph189{R1Metric,WedgeOrder,RetainedWidth,HighThirdLayer,RootWidth}.lean "$out"/
cp "$src"/../lowblock/Graph189ColumnCancel.lean "$out"/
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  for module in Graph189R1Metric Graph189WedgeOrder Graph189RetainedWidth Graph189HighThirdLayer Graph189ColumnCancel Graph189RootWidth; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' _ "$out"
