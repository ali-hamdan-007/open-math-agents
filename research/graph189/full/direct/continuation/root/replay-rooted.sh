#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with its dependencies built}
project=$(cd "$project" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cp "$source_dir"/{Graph189RootedOreCount,Graph189RootedTrace,RootedTraceAudit}.lean "$build/"
cp "$source_dir/../order/Graph189RootedPath.lean" "$build/"
cp "$source_dir/../verify"/{Graph189WedgeOrder,Graph189WedgeCorollary}.lean "$build/"
cp "$source_dir/../../factor/Graph189R1Metric.lean" "$build/"
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  for mod in Graph189R1Metric Graph189RootedPath Graph189RootedOreCount Graph189WedgeOrder Graph189WedgeCorollary Graph189RootedTrace; do
    lean -j1 -DwarningAsError=true -o "$mod.olean" "$mod.lean"
  done
  lean -j1 -DwarningAsError=true RootedTraceAudit.lean
' _ "$build"
