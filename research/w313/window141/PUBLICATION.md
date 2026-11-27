# Publication manifest

**Subject** — Transportable upper-bound branches for W(3,13) on 160 points, including two normalized R2-H2 tuples. The full equality and all complete R1/R2 hypotheses remain outside scope.

**Publish the modular bundle** — Preserve the relative paths in this table, starting at the local directory `parallel/ramsey`. The proof modules import Lean only. Build sequentially with Lean 4.33.1 and `window141/verify.sh --old`. Do not concatenate the proof modules for the primary release. The combined width-141 file exceeded the local build memory limit, while both separate modules compiled.

| Local paths | Role |
| --- | --- |
| `Green160NearWitness.lean` | Original checker template and 160-point progression/reflection definitions. |
| `window141/Green141WindowCore.lean`, `window141/Green141Window43.lean`, `window141/Green141Window73.lean` | Shared width-141 checker and both translated/reflected branches. |
| `window141/Green130WindowCore.lean`, `window141/Green130Window64.lean`, `window141/Green130R2Bridge.lean` | Width-130 checker, branch, and two exact R2-H2 fiber theorems. |
| `extension160/Green160FourRed.lean` | Previously verified four-red branches, included by `verify.sh --old` and by the stated coverage bound. |
| `window141/verify.sh` | Build all included proofs from the text files. |
| `search160.cpp`, `window141/make_window.py`, `window141/window.tail` | Regenerate the compact tape sources. |
| `window141/coverage.py`, `window141/r2_screen.py` | Reproduce coverage fractions and R2-tuple counts, or export DIMACS clauses. |
| `window141/README.md`, `window141/PUBLICATION.md`, `window141/lean43.log`, `window141/lean73.log`, `window141/lean130-64.log`, `window141/lean-r2-bridge.log`, `window141/r2-screen.log` | Scope, build instructions, provenance and audits. |

The prior `Green160FourRed.lean` remains at its original local path and has SHA-256 `df39c2d69f5ece98cd4dc3020911dc6b04dde99239600f805ec9db496e858f30`.

The exact 75-clause subset consists of all twenty translations and reflections of seed 73, ten translations and reflections of seed 43, the width-130 shape for starts 51 through 63, and both prior branches. Reproduce the 96.189714595701% fraction with `python3 window141/coverage.py 73:20 43:10 --old --r2 51:63`. Export all 126 certified clauses with `python3 window141/coverage.py 73:20 43:20 --old --r2 51:94 --dimacs`.

## Relation to merged reductions

- [R1 / PR #3990](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3990) fixes a closest red to the center and the blues between that red point and its reflection. It does not prescribe a checked four-red seed. The local 100,000-node search cap was reached on all seven R1 subbranches.
- [R2 / PR #4300](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4300) fixes red points on the four length-13 rays of common difference 13. Its H2 hypothesis includes the normalized heights ((5,4,5,4)) and ((6,5,6,5)). The bridge proves both fibers under the exact ray, no-red-triple and shorter-step hitting assumptions. The exhaustive R2 tuple screen reports 3,438 H1 tuples, 4,924 H2 tuples and 4,924 H3 tuples. Of these, the two H2 tuples are the only immediate eliminations from the complete 126-clause set under unit propagation. The other certified clauses can be applied deeper in a search.

Use a supplemental research bundle on the fork, rather than presenting the files as a complete `proofs/Green14.W_3_13.lean` submission. The certified 160-point exclusions are reusable premises for continued upper-bound search.
