# Erdős 1082 exact two-case Lean proof

The target is `Erdos1082.erdos_1082.parts.i.R1.H2.R1.H4.R1.H2.R1.H3.R1.H2`, the H2 statement in merged [reduction #5040](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5040). The statement excludes five-point base codes 157 and 123 from any ten-point, four-distance plane configuration satisfying the reduction's hypotheses.

## Build and audit

Run `./build_leaf.sh` with Lean 4.33.1 and the pinned Mathlib cache. Set `OMA_REPO` to the open-math-agents checkout if the latter is not next to this workspace. The code 157 modules are listed in `LEAN-MANIFEST.md`. The table workers run sequentially and reuse completed local module objects. For a source-only recompilation, build in a fresh extracted directory.

The pinned Formal Conjectures revision is `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`.

The following add the code 123 case and the upstream proposition.

| Source | Role |
| --- | --- |
| `Normalize123.lean`, `Transport123.lean`, `Positive123.lean` | Normalize arbitrary base coordinates and use a horizontal reflection to handle both signs using one table |
| `CandidateCount.lean` | Check represented fourth-distance buckets and carry the resulting cardinality bound to real points |
| `Rows123.lean` | Explicit rational radical coordinates for the surviving label assignments, with both signed point counts kernel-checked |
| `Cover123.lean` | Sound table lookup and geometric bound from coverage |
| `build123-blocks.sh` | Generate and kernel-check one independent module for each of 32 blocks of 32 assignments |
| `Assembly123.lean` | Combine all coverage blocks |
| `ExtensionBound123.lean` | Prove the normalized result for an arbitrary realization |
| `Digits.lean` | Decode the ten digits of both published base codes |
| `TargetGeometry.lean` | Transfer the two counts to the actual plane and pinned distance-set definitions |
| `build_geometry_dependencies.py` | Compile the few missing pinned upstream geometry imports |
| `ExactLeafGeometry.lean` | State the exact upstream H2 proposition and attach the geometric proof |
| `ExactLeaf.lean` | Unconditional endpoint and axiom audit, using the exact H2 proposition |

Code 157 allows at most three extra points, and code 123 allows at most four. Each configuration in H2 would need five extra points. The checker uses rational computations inside Lean's kernel. It represents real algebraic numbers by rational coefficient polynomials with verified evaluation and nonzero witnesses. No compiled-code equality oracle is used.
