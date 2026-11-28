#!/usr/bin/env bash
# From the pinned Formal Conjectures checkout, check the registered declaration
# against the independently compiled Graph189Unconditional module.
set -euo pipefail
build="$(cd "$1" && pwd)"
proof_dir="$(cd "$(dirname "$0")/../root/bounded-order" && pwd)"
want=9097e2f90e66d2f6244209cb1c07f7120d17ec53
test "$(git rev-parse HEAD)" = "$want"
lake build FormalConjectures.WrittenOnTheWallII.GraphConjecture189
lake env bash -c 'export LEAN_PATH="$LEAN_PATH:$1"; lean -j1 "$2"' _ "$build" "$proof_dir/Graph189OriginalSolution.lean" | tee "$build/registered-solution.log"
grep -Fqx "'OMA.solution' depends on axioms: [propext, Classical.choice, Quot.sound]" "$build/registered-solution.log"
