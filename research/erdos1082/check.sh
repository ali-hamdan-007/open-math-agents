#!/usr/bin/env bash
set -eu
here=$(cd "$(dirname "$0")" && pwd)
repo="${OMA_REPO:-$(cd "$here/../.." && pwd)}"
if [[ ! -d "$repo/.oma/formal-conjectures" && -d "$repo/open-math-agents/.oma/formal-conjectures" ]]; then
  repo="$repo/open-math-agents"
fi
fc="$repo/.oma/formal-conjectures"
if [[ ! -d "$fc" ]]; then
  echo 'Set OMA_REPO to the open-math-agents checkout with the pinned .oma dependencies.' >&2
  exit 1
fi
paths="$(printf '%s:' "$fc"/.lake/packages/*/.lake/build/lib/lean)"
export LEAN_PATH="$here:${paths%:}"
export ELAN_HOME="$repo/.oma/elan"
exec "$ELAN_HOME/bin/elan" run leanprover/lean4:v4.33.1 lean "$@"
