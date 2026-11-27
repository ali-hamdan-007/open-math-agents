#!/usr/bin/env bash
# Run with the pinned Mathlib cache in open-math-agents/.oma available.
set -eu
cd "$(dirname "$0")"
mode="${1:-}"
build() {
  if [[ "$mode" != --resume || ! -f "$1.olean" ]]; then
    ./check.sh -o "$1.olean" "$1.lean"
  fi
}
for module in RadicalAlgebra ExtensionCertificate NormalForms Bounds Frame Normalize157 Transport157 ExtensionBound157; do
  build "$module"
done
python generate_blocks.py
for source in Check157Block*.lean Checked157_*.lean; do
  build "${source%.lean}"
done
build Assembly157
build Code157
