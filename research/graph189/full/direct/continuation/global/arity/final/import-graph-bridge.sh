#!/usr/bin/env bash
set -eu
p=/tmp/ali189-active.CE0Lol
live() { test -e "$p/LIVE" && test ! -e "$p/PAUSE" && test ! -e "$p/HALT"; }
live || exit 3
here="$(cd "$(dirname "$0")" && pwd)"
fresh="$(mktemp -d "$here/graph-import-XXXXXX")"
wk=/workspace/scratch/6893ca6bed01
runtime=/tmp/ali-g189-nov28.CK3m0v/cutlean/runtime
export LD_LIBRARY_PATH="$runtime${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LEAN_PATH="$fresh:$here:$p/root:$p/verify:$p/order:$p/lowblock:/tmp/ali-g189-nov28.CK3m0v/split/overlay:$runtime/modules:$wk/parallel/fresh-wow:$wk/parallel/fresh-wow/focused:$wk/parallel/new-graph:$wk/parallel/new-graph/focused:$wk/parallel/ramsey/focused:$(cat "$wk/parallel/pell/lean-path.txt")"
lean="$wk/open-math-agents/.oma/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
cd "$fresh"
cp "$here/Graph189TerminalGraphAudit.lean" .
exec 9>"$p/cold-lean.lock"
flock 9
live || exit 3
"$lean" --version
"$lean" -j1 -DwarningAsError=true -o Graph189TerminalGraphAudit.olean Graph189TerminalGraphAudit.lean
