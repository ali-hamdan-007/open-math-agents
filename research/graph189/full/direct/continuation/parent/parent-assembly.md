# Assembling the exact Graph 189 parent

Graph189ParentAssembly.lean in this directory is a conditional theorem. Its conclusion is exactly the type of the registered conjecture, including the universe-polymorphic vertex type and the original maximum-even-distance hypothesis. The proof supplies the cut-vertex case and takes two two-connected results as explicit arguments.

Let k be the second-smallest degree, with repetitions, and n the number of vertices. The first argument requires a Hamilton path for qualifying two-connected graphs with 2k+3 ≤ n ≤ 3k+2. The second concerns qualifying two-connected graphs with n ≥ 3k+3 and the local obstruction in H2 of the child reduction. The definition specifies three vertices u,w,v forming an induced path whose middle degree exceeds both other degrees, failure of a degree-sum inequality, and a bound on n. The paper proof covers both ranges. The formal proof connecting its graph arguments and the finite contradictions to these two propositions remains to be supplied. A proof for all two-connected graphs also fills both arguments.

The source is generated from three files, with the following exact byte hashes.

| Component | Source | SHA-256 |
|---|---|---|
| Original R2 | [Upstream reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/da942fcbcd485eb0c2abd945b618003f9eee41bb/reductions/WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.lean) | 5c5b95a2df5bb7925351320090bf5375bd06b7f32593e568e20ab30a1fa1cc64 |
| Cut-vertex proof | [Ali's R2.H1 proof](https://github.com/ali-hamdan-007/open-math-agents/blob/59cd570c116fae32abc3eac22d6ac667473dd480/proofs/WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H1.lean) | 6a8ec853732119dd87acdc0b33620eaa4a8540a5cdd362a3398c1d202bd34ead |
| Two-connected reduction | [Ali's R2.H2.R1](https://github.com/ali-hamdan-007/open-math-agents/blob/678de7fa0498a2dc598dde49a0b6fc4b76b0e9df/reductions/WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1.lean) | d06e932f3e7703c9ed437a6b13aa5c22c732ef700a49e5002e9646bebb766477 |

Use the script with saved copies of these sources in table order.

```sh
python3 assemble.py original-r2.lean cut-vertex.lean child.lean Graph189ParentAssembly.lean
```

The original R2 is credited to carl2sheriff and cites instrumentally reused work from computerfreak97 and philipsaint. Its credits remain in the generated file. The child reduction in PR 18811 passed the project checker. The research assembly has no upstream submission or checker verdict.

For focused testing, make-focused.py reconstructs the binder and conclusion from the pinned problem file and replaces the problem-wide import with the focused degree, distance and list modules. It introduces a polymorphic abbreviation of the proposition, without introducing a conjecture as an axiom. On a pinned checkout with the full imports available, use Graph189ParentAssembly.lean as generated.
