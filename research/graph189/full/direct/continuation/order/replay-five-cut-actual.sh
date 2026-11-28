#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
continuation_dir=$(dirname "$source_dir")
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with built mathlib}
project=$(cd "$project" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
cp "$continuation_dir/root"/Graph189{CrossPort,CrossOrder,SeparatorCover,HighPredecessor,NineCutDebit}.lean "$build_dir/"
cp "$continuation_dir/verify"/Graph189{R1Metric,WedgeOrder,HighThirdLayer,RetainedWidth,RootWidth,FiveCutDebit}.lean "$build_dir/"
cp "$continuation_dir/lowblock/Graph189ColumnCancel.lean" "$build_dir/"
cp "$source_dir"/{Graph189CutSides,Graph189MinimumCut,Graph189MinimumCutOrder,Graph189DegreeCeiling,Graph189MaximumDegree,Graph189TrimmedRows,Graph189MixedDebit,Graph189LowMixedCut,Graph189ActualRootWidthBounds,Graph189FiveCutActual,ImportFiveCutActual}.lean "$build_dir/"
cd "$project"
lake env bash -c '
set -euo pipefail
export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
cd "$1"
for mod in Graph189SeparatorCover Graph189CrossPort Graph189CrossOrder Graph189HighPredecessor Graph189R1Metric Graph189CutSides Graph189MinimumCut Graph189WedgeOrder Graph189MinimumCutOrder Graph189DegreeCeiling Graph189MaximumDegree Graph189NineCutDebit Graph189TrimmedRows Graph189MixedDebit Graph189LowMixedCut Graph189HighThirdLayer Graph189RetainedWidth Graph189ColumnCancel Graph189RootWidth Graph189ActualRootWidthBounds Graph189FiveCutDebit Graph189FiveCutActual; do
  lean -j1 -DwarningAsError=true -o "$mod.olean" "$mod.lean"
done
lean -j1 -DwarningAsError=true ImportFiveCutActual.lean
' _ "$build_dir"
