#!/usr/bin/env bash
set -eu
source_dir=$(cd "$(dirname "$0")" && pwd)
project_dir=${1:?Pass the pinned Mathlib project directory}
build_dir=${2:-$(mktemp -d)}
mkdir -p "$build_dir"
build_dir=$(cd "$build_dir" && pwd)
cp "$source_dir"/Graph189{FiniteDomain,ScalarReplay,TerminalQuotas}.lean "$build_dir/"
cd "$project_dir"
lake env bash -c '
  set -eu
  cd "$1"
  export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
  lean --version
  for module in Graph189FiniteDomain Graph189TerminalQuotas Graph189ScalarReplay; do
    lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
  done
' bash "$build_dir"
