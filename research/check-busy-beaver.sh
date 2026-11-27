#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if (( $# > 1 )); then
  printf 'Usage: %s [open-math-agents checkout]\n' "$0" >&2
  exit 2
fi
checkout="$(git -C "${1:-$here}" rev-parse --show-toplevel)"
project="${OMA_FC:-$checkout/.oma/formal-conjectures}"
pin="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["meta"]["upstreamCommit"])' \
  "$checkout/data/catalog.json")"
if [[ "$(git -C "$project" rev-parse HEAD)" != "$pin" ]]; then
  printf 'Expected Formal Conjectures at %s. Run tools/oma.sh setup first.\n' "$pin" >&2
  exit 1
fi

build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
if [[ -x "$checkout/.oma/elan/bin/elan" ]]; then
  export ELAN_HOME="$checkout/.oma/elan"
  elan="$ELAN_HOME/bin/elan"
else
  elan="$(command -v elan)"
fi
toolchain="$(cat "$project/lean-toolchain")"

# Copy the pinned definitions and the existing normalization theorem verbatim.
# The umbrella imports pull in all Mathlib, so load only the needed modules here.
mkdir -p "$build/FormalConjectures/Wikipedia" "$build/OMAReductions"
git -C "$project" show "$pin:FormalConjectures/Wikipedia/BusyBeaver.lean" > "$build/upstream.lean"
git -C "$checkout" show HEAD:reductions/BusyBeaver.BB_4.R1.lean > "$build/reduction.lean"
{
  printf 'import FormalConjecturesForMathlib.Computability.TuringMachine.BusyBeavers\n'
  printf 'import Mathlib.Data.Fintype.EquivFin\n'
  awk '/^universe u v$/ { copy=1 } copy && /^\/--$/ { exit } copy { print }' "$build/upstream.lean"
  awk '/^noncomputable def BB / { print; getline; print; exit }' "$build/upstream.lean"
  printf '\nend BusyBeaver\n'
} > "$build/FormalConjectures/Wikipedia/BusyBeaver.lean"
{
  cat <<'LEAN'
import FormalConjectures.Wikipedia.BusyBeaver
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
LEAN
  awk '/^namespace OMA.R_BusyBeaver_BB_4_R1$/ { copy=1 } copy && /^theorem main / { exit } copy { print }' \
    "$build/reduction.lean"
  printf 'end OMA.R_BusyBeaver_BB_4_R1\n'
} > "$build/OMAReductions/R_BusyBeaver_BB_4_R1.lean"
cp "$here/BusyBeaverStrictGrowth.lean" "$here/BusyBeaverSuccessor.lean" "$build/"

cd "$project"
"$elan" run "$toolchain" lake build +FormalConjecturesForMathlib.Computability.TuringMachine.BusyBeavers \
  +Mathlib.Data.Fintype.EquivFin +Mathlib.Data.Fintype.Option +Mathlib.Data.Fintype.Sum \
  +Mathlib.Data.Finite.Prod +Mathlib.Order.ConditionallyCompleteLattice.Finset
export LEAN_PATH="$build:$("$elan" run "$toolchain" lake env printenv LEAN_PATH)"
for module in FormalConjectures/Wikipedia/BusyBeaver OMAReductions/R_BusyBeaver_BB_4_R1 \
  BusyBeaverStrictGrowth BusyBeaverSuccessor; do
  "$elan" run "$toolchain" lean --root="$build" -o "$build/$module.olean" "$build/$module.lean"
done
