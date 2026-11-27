#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "$0")" && pwd)
ramsey=$(cd "$work/../.." && pwd)
output=$(realpath -m "${1:-Green14-W3-13-R2-adjacent.tar.gz}")
cd "$ramsey"
files=(
    Green160NearWitness.lean search160.cpp
    window141/Green130WindowCore.lean window141/Green130Window64.lean
    window141/Green130R2Bridge.lean
    r2adjacent/Green137WindowCore.lean r2adjacent/Green137Window27.lean
    r2adjacent/Green150WindowCore.lean r2adjacent/Green150Window14.lean
    r2adjacent/GreenR2Adjacent.lean r2adjacent/GreenR2AdjacentFull.lean
    r2adjacent/make_window.py r2adjacent/window.tail r2adjacent/screen.py
    r2adjacent/verify_full.sh r2adjacent/README.md r2adjacent/lean.log r2adjacent/bridge.log
    r2adjacent/edge154/Green154Edge*.lean
    r2adjacent/edge154/generate.py r2adjacent/edge154/verify.sh r2adjacent/edge154/package.sh
    r2adjacent/edge154/PUBLICATION.md r2adjacent/edge154/search.log
    r2adjacent/edge154/lean.log r2adjacent/edge154/final-audit.log
)
tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - "${files[@]}" |
    gzip -n > "$output"
printf '%s\n' "$output"
