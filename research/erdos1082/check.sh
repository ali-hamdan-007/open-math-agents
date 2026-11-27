#!/usr/bin/env bash
set -eu
here=$(cd "$(dirname "$0")" && pwd)
fc=$(cd "$here/../../open-math-agents/.oma/formal-conjectures" && pwd)
paths="$(printf '%s:' "$fc"/.lake/packages/*/.lake/build/lib/lean)"
export LEAN_PATH="$here:${paths%:}"
export ELAN_HOME="$fc/../elan"
exec "$ELAN_HOME/bin/elan" run leanprover/lean4:v4.33.1 lean "$@"
