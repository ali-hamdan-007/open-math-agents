# Lean checkpoint for Erdős 1082, code 157

The target leaf is `Erdos1082.erdos_1082.parts.i.R1.H2.R1.H4.R1.H2.R1.H3.R1.H2` from reduction #5040. It covers two base codes, 123 and 157. This bundle's endpoint `Erdos1082.code157_bound` is the code 157 branch in real pair coordinates. Its conclusion bounds the number of additional points by three for any common fourth squared distance. Five additional points would be necessary for a ten-point set. The literal reduction wrapper and the complete code 123 certificate remain separate work.

The authoritative input is these source files.

| File | Verified role |
| --- | --- |
| `RadicalAlgebra.lean` | Exact rational representations at roots of s² = 3 and z³ = 3z + 1, with sound inverse witnesses |
| `ExtensionCertificate.lean` | Sound finite classification of one affine squared-distance system |
| `NormalForms.lean` | Encodes both base codes and transports real squared-distance equations to affine systems |
| `Bounds.lean` | Exhaustive base-four labeling, kernel block interface and finite cardinality transport for code 157 |
| `Frame.lean` | Injective scaling and frame for any equilateral base triple |
| `Normalize157.lean` | Cubic normal form derived directly from code 157's squared distances |
| `Transport157.lean` | Normalization from arbitrary original real pair coordinates |
| `ExtensionBound157.lean` | Complete geometric exclusion conditional on the finite block checks |
| `generate_blocks.py` | Deterministically generates `Check157Block04.lean` through `Check157Block31.lean` and `Checked157_0.lean` through `Checked157_7.lean` |
| `Assembly157.lean` | Covers all 1,024 assignments by the 32 proved blocks |
| `Code157.lean` | Audits the final unconditional branch theorem |

Run `./build157.sh` from this directory for a clean build using the existing pinned Mathlib caches and Lean 4.33.1. The wrapper `check.sh` locates those caches relative to this directory. Use `./build157.sh --resume` to reuse the compiled modules from a previously verified checkpoint. The generated files need only one Lean worker. Two concurrent workers exceeded the available memory. Block proofs use `decide +kernel`, with no native oracles.

The separate 123 checkpoint is `Normalize123.lean`, `CandidateCount.lean`, `Rows123.lean`, `Cover123.lean`, and `Transport123.lean`. The exact candidate counts are proved in `Rows123.lean`; the exhaustive cover table is still needed. One signed table suffices by reflecting the horizontal axis and negating s.
