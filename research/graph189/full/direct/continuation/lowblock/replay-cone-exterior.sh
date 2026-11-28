#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with built mathlib}
project=$(cd "$project" && pwd)
exterior="$src/../sep/cover/final82/lean"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cp "$src/../root"/Graph189{CrossPort,CrossOrder,SeparatorCover,HighPredecessor,AtomCounts,CutCorner,Atom,Removable,CriticalConnectivity}.lean "$out/"
cp "$src/../verify"/Graph189{R1Metric,WedgeOrder,RootedPath}.lean "$out/"
cp "$src/../order"/Graph189{CutSides,MinimumCut,MinimumCutOrder}.lean "$out/"
cp "$exterior/upstream/Graph189TraceClosurePublic.lean" "$out/"
cp "$exterior"/Graph189{ExteriorGap,ContactIntervals,MatchedOrder,ExteriorSpacing,ContactColumns,ExteriorDegree,HighExteriorDegree,ExteriorHalf,MidpointExchange}.lean "$out/"
cp "$src"/Graph189{UniversalCycle,CompletionConnectivity,ExteriorDegreeCycle,ExteriorPopulation,SingleExteriorShift,DoubleExteriorShift,IndependentExterior,ConeNontrivial,ConeExteriorCycle,HighMinimumGap,CriticalExterior,SingletonDeletion,MinimumDeletionExterior,MinimumDeletionSharp,LongestCycleMaximum,CriticalOrderViaCycles}.lean "$out/"
modules=(Graph189SeparatorCover Graph189CrossPort Graph189CrossOrder Graph189HighPredecessor
  Graph189R1Metric Graph189CutSides Graph189MinimumCut Graph189WedgeOrder Graph189MinimumCutOrder
  Graph189UniversalCycle Graph189CompletionConnectivity Graph189RootedPath Graph189ExteriorDegreeCycle
  Graph189ExteriorPopulation Graph189AtomCounts Graph189CutCorner Graph189Atom Graph189Removable Graph189CriticalConnectivity
  Graph189TraceClosurePublic Graph189ExteriorGap Graph189ContactIntervals
  Graph189MatchedOrder Graph189ExteriorSpacing Graph189ContactColumns Graph189ExteriorDegree Graph189SingleExteriorShift
  Graph189IndependentExterior Graph189ConeNontrivial Graph189ConeExteriorCycle Graph189HighExteriorDegree Graph189ExteriorHalf
  Graph189MidpointExchange Graph189DoubleExteriorShift Graph189HighMinimumGap Graph189CriticalExterior
  Graph189SingletonDeletion Graph189MinimumDeletionExterior Graph189MinimumDeletionSharp Graph189LongestCycleMaximum Graph189CriticalOrderViaCycles)
cd "$project"
lake env bash -c '
  set -euo pipefail
  project=$PWD
  IFS=: read -ra paths <<< "${LEAN_PATH:-}"
  export LEAN_PATH="$1"
  for path in "${paths[@]}"; do
    [[ -n "$path" ]] || continue
    [[ "$path" = /* ]] || path="$project/$path"
    LEAN_PATH="$LEAN_PATH:$path"
  done
  cd "$1"
  shift
  for module in "$@"; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' _ "$out" "${modules[@]}"
