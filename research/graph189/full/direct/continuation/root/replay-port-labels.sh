#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with its dependencies built}
project=$(cd "$project" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$src"/Graph189{SupportClassification,PortLabels}.lean "$tmp/"
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  for mod in Graph189SupportClassification Graph189PortLabels; do
    lean -j1 -DwarningAsError=true -o "$mod.olean" "$mod.lean"
  done
' _ "$tmp"
