#!/usr/bin/env bash
set -euo pipefail

: "${OMA_FC:?Set OMA_FC to the prepared Formal Conjectures checkout}"
external="$(cd "${1:?Usage: check.sh /path/to/erdos307}" && pwd)"
project="$(cd "$(dirname "$0")" && pwd)"
fc="$(cd "$OMA_FC" && pwd)"
revision="$(git -C "$external" rev-parse HEAD)"
expected=36c3b7979a77e003fcf47016e41f2f7133495415
if [[ "$revision" != "$expected" ]]; then
  printf 'Expected Bonfioli commit %s, found %s\n' "$expected" "$revision" >&2
  exit 1
fi
if [[ ! -f "$external/lean/Erdos307/FocusedImports.lean" ]]; then
  printf 'Apply bonfioli-v1.76.2-lean-v4.33.1.patch to the external checkout before running.\n' >&2
  exit 1
fi
if [[ -d "$fc/../elan/bin" ]]; then
  export ELAN_HOME="$(cd "$fc/../elan" && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
lake_bin="${LAKE_BIN:-lake}"
build="$(mktemp -d)"
trap 'rm -rf -- "$build"' EXIT
mkdir -p "$build/Erdos307"
cd "$fc"
case "$("$lake_bin" env lean --version)" in
  *'version 4.33.1'*) ;;
  *) printf 'This port requires Lean v4.33.1.\n' >&2; exit 1 ;;
esac
lean="$("$lake_bin" env sh -c 'command -v lean')"
lean_path="$("$lake_bin" env printenv LEAN_PATH)"
export LEAN_PATH="$build:$lean_path"
for name in FocusedImports Rigidity Barrier Capstone Extremal Numeral Closed NonSquare Sixty; do
  printf 'Checking Erdos307.%s\n' "$name"
  "$lean" --root="$external/lean" -o "$build/Erdos307/$name.olean" \
    "$external/lean/Erdos307/$name.lean"
done
for name in PrimeBudget Erdos307CrossCoprime Erdos307CoprimeBarrier; do
  printf 'Checking %s\n' "$name"
  "$lean" --root="$project" -o "$build/$name.olean" "$project/$name.lean"
done
"$lean" --root="$project" "$project/CoprimeSixty.lean"
