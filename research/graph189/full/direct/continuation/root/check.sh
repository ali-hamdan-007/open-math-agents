#!/bin/bash
set -eu
work=$(cd "$(dirname "$0")" && pwd)
r=/workspace/scratch/6893ca6bed01
runtime=/tmp/ali-g189-nov28.CK3m0v/cutlean/runtime
export LD_LIBRARY_PATH="$runtime${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LEAN_PATH="$work:$runtime/modules:$r/parallel/fresh-wow:$r/parallel/fresh-wow/focused:$r/parallel/new-graph:$r/parallel/new-graph/focused:$r/parallel/ramsey/focused:$(cat "$r/parallel/pell/lean-path.txt")"
cd "$work"
exec "$r/open-math-agents/.oma/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean" -j1 "$@"
