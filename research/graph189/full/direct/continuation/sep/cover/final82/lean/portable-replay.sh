#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_PROJECT:?Set MATHLIB_PROJECT to a built project using the recorded mathlib revision}"
project=$(cd "$MATHLIB_PROJECT" && pwd)
manifest=
if [[ ${1:-} == --full ]]; then manifest="$source_dir/full-modules.txt"; fi
output="$source_dir/portable-build"
mkdir -p "$output"
cp "$source_dir"/upstream/*.lean "$source_dir"/Graph189*.lean "$output/"
cd "$project"
lake env bash -eu -o pipefail -c '
  original=$PWD
  expanded=
  IFS=: read -ra paths <<< "${LEAN_PATH:-}"
  for path in "${paths[@]}"; do
    [[ -n $path ]] || continue
    [[ $path == /* ]] || path="$original/$path"
    expanded="${expanded:+$expanded:}$path"
  done
  cd "$1"
  export LEAN_PATH="$PWD${expanded:+:$expanded}"
  modules=(Graph189TraceClosurePublic Graph189GatewayRank Graph189GatewaySelection
    Graph189TerminalLeafClosure Graph189LeafEndpoints Graph189LeafStrip Graph189PrescribedClosure
    Graph189PrescribedBatch Graph189ExteriorClosure Graph189ExteriorGap)
  if [[ -n $2 ]]; then mapfile -t modules < "$2"; fi
  for module in "${modules[@]}"; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' _ "$output" "$manifest"
