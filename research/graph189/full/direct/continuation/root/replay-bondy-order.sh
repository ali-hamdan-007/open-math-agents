#!/usr/bin/env bash
# Run inside an environment with the indicated pinned projects already built.
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
: "${BONDY_PROOF:?Supply the single-file proof from OMA PR 7971}"
: "${FORMAL_CONJECTURES:?Supply the pinned formal-conjectures checkout}"
: "${MATHLIB_PROJECT:?Supply a built project at the pinned mathlib revision}"
build=$(mktemp -d)
cp "$base/Graph189LinkedExterior.lean" "$base/Graph189BondyOrder.lean" "$build/"
python3 "$base/extract_bondy_core.py" "$BONDY_PROOF" "$FORMAL_CONJECTURES" "$build/Graph189BondyCore.lean"
cd "$MATHLIB_PROJECT"
lake env bash -eu -o pipefail -c '
  project=$PWD
  paths=
  IFS=: read -ra entries <<< "$LEAN_PATH"
  for entry in "${entries[@]}"; do
    [[ $entry == /* ]] || entry="$project/$entry"
    paths="${paths:+$paths:}$entry"
  done
  cd "$1"
  export LEAN_PATH="$PWD:$paths"
  lean -j1 -DwarningAsError=true -o Graph189LinkedExterior.olean Graph189LinkedExterior.lean
  lean -j1 -o Graph189BondyCore.olean Graph189BondyCore.lean
  lean -j1 -DwarningAsError=true -o Graph189BondyOrder.olean Graph189BondyOrder.lean
' _ "$build"
echo "Compiled modules: $build"
