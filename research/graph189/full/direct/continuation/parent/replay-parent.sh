#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with its dependencies built}
project=$(cd "$project" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$src/Graph189ParentAssembly.lean" "$tmp/"
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  lean -j1 -o Graph189ParentAssembly.olean Graph189ParentAssembly.lean
  printf "%s\n" "import Graph189ParentAssembly" "#print axioms Graph189ParentAssembly.parent_of_two_connected_cases" | lean -j1 --stdin
' _ "$tmp"
