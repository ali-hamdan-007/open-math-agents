#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with dependencies built}
project=$(cd "$project" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cp "$src"/{Graph189SeparatorCover,SeparatorCoverAudit,Graph189CrossPort,CrossPortAudit,Graph189CrossOrder,CrossOrderAudit,Graph189LayerCover,LayerCoverAudit,Graph189LayerCutoff,LayerCutoffAudit}.lean "$build/"
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  lean -j1 -DwarningAsError=true -o Graph189SeparatorCover.olean Graph189SeparatorCover.lean
  lean -j1 -DwarningAsError=true SeparatorCoverAudit.lean
  lean -j1 -DwarningAsError=true -o Graph189CrossPort.olean Graph189CrossPort.lean
  lean -j1 -DwarningAsError=true CrossPortAudit.lean
  lean -j1 -DwarningAsError=true -o Graph189CrossOrder.olean Graph189CrossOrder.lean
  lean -j1 -DwarningAsError=true CrossOrderAudit.lean
  lean -j1 -DwarningAsError=true -o Graph189LayerCover.olean Graph189LayerCover.lean
  lean -j1 -DwarningAsError=true LayerCoverAudit.lean
  lean -j1 -DwarningAsError=true -o Graph189LayerCutoff.olean Graph189LayerCutoff.lean
  lean -j1 -DwarningAsError=true LayerCutoffAudit.lean
' _ "$build"
