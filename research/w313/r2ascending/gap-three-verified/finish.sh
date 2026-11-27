#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
root=/workspace/scratch/6893ca6bed01
export LEAN_PATH="$PWD:$root/parallel/ramsey/focused:$(cat "$root/parallel/pell/lean-path.txt")"
LEAN="$root/open-math-agents/.oma/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
./build.sh
for m in GapThreeGeometry GapThreeVerified; do
    "$LEAN" -o "$m.olean" "$m.lean" | tee "$m.log"
    test -f "$m.olean"
done
if [[ -n "${GAP_TWO_DIR:-}" ]]; then
    export LEAN_PATH="$GAP_TWO_DIR:$LEAN_PATH"
    for m in H3Remainder H3LiteralAudit; do
        "$LEAN" -o "$m.olean" "$m.lean" | tee "$m.log"
        test -f "$m.olean"
    done
fi
