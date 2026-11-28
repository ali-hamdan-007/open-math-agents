#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
project=${OMA_FC:?Set OMA_FC to the pinned formal-conjectures checkout with its dependencies built}
project=$(cd "$project" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
case "${1:-full}" in
  full)
    module=Graph189ParentAssembly
    cp "$src/$module.lean" "$tmp/" ;;
  focused)
    module=Graph189ParentFocused
    python3 "$src/make-focused.py" "$src/Graph189ParentAssembly.lean" \
      "$project/FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean" "$tmp/$module.lean" ;;
  *)
    echo "Usage: replay-parent.sh [full|focused]" >&2
    exit 2 ;;
esac
cd "$project"
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  cd "$1"
  lean -j1 -o "$2.olean" "$2.lean"
  printf "import %s\n#print axioms Graph189ParentAssembly.parent_of_two_connected_cases\n" "$2" | lean -j1 --stdin
' _ "$tmp" "$module"
