#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
proofs=$(cd "$src/../../.." && pwd)
project=${1:?Pass the pinned Mathlib project directory}
out=${2:-$(mktemp -d)}
mkdir -p "$out"
out=$(cd "$out" && pwd)
cp "$src"/Graph189{FiniteDomain,InfiniteTail,WidthWindows,WindowCover,LargeDegree,EightCutoff,SmallWindowCover,ValidBand,ScalarConclusion}.lean "$out/"
cp "$proofs/root/Graph189NineCutDebit.lean" "$proofs/verify/Graph189FiveCutDebit.lean" "$out/"
cd "$project"
lake env bash -c '
  set -eu
  cd "$1"
  export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
  lean --version
  for module in Graph189FiniteDomain Graph189InfiniteTail Graph189WidthWindows Graph189WindowCover Graph189LargeDegree Graph189NineCutDebit Graph189EightCutoff Graph189FiveCutDebit Graph189SmallWindowCover Graph189ValidBand Graph189ScalarConclusion; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' bash "$out"
