# Verified ranges of Graph 189

The pinned Lean kernel checked each of the following graph-facing conclusions. Here n is the number of vertices, k is the second-smallest degree counting repetitions, δ is the minimum degree and κ is the vertex connectivity. Every result uses the registered connectedness and even-distance hypotheses.

| Additional hypotheses | Conclusion and Lean source |
|---|---|
| Exact moderate child, 2k+3≤n≤3k+2, every k | A Hamiltonian path. [ModerateComplete.moderate](Graph189ModerateComplete.lean) has the registered child type and passed [independent kernel replay](https://github.com/ali-hamdan-007/open-math-agents/actions/runs/46135948159/job/140951158759). |
| k=5, or k=6 and a degree-two vertex, κ≥2 | A Hamiltonian path at every order. [FiveOriginal](../verify/Graph189FiveOriginal.lean) and [SixOrder](../verify/Graph189SixOrder.lean) passed [independent replay](https://github.com/ali-hamdan-007/open-math-agents/actions/runs/46134769244/job/140947485627). |
| k≥7, n≤3k+2 | A Hamiltonian path in the original graph. [ModerateSeven.original](Graph189ModerateSeven.lean) |
| k=6, κ≥3 | A Hamiltonian path at every order. [SixThreeConnected.traceable](Graph189SixThreeConnected.lean) |
| k=6, κ≥2, δ≥3, n≤20 | A Hamiltonian path. [SixMinimumThree.traceable](Graph189SixMinimumThree.lean) |
| k=4 | A Hamiltonian path at every order. [FourOriginal.traceable_four](../verify/Graph189FourOriginal.lean) |
| k=5, δ=5 | A Hamiltonian path at every order. [FiveTiedOriginal.traceable_tied_five](../verify/Graph189FiveTiedOriginal.lean) |
| k=15 or 16, κ≥7, or k=17 or 18, κ≥6 | A Hamiltonian path at every order. [SevenIndexTraceable.traceable_sector](../lowblock/Graph189SevenIndexTraceable.lean) |
| κ≥2, k≥26, some path omits at most k+1−floor((k+2)/4) vertices | A Hamiltonian path. This is the terminal path-length criterion for the two-side arguments below connectivity five. [OrdinaryOmission.traceable_of_near](Graph189OrdinaryOmission.lean) |
| κ≥2, δ=2, k≥7 | A Hamiltonian path at every order. [DegreeTwoOriginal.traceable](Graph189DegreeTwoOriginal.lean) |
| κ≥2, k≥7, n≤4k−6 | A Hamiltonian path. In particular this covers the entire moderate parent interval for k≥8, and n≤22 at k=7. [ModerateEight.original_below_four and original_moderate](Graph189ModerateEight.lean) |
| κ≥2, k≥12, n≤3k+2 | A Hamiltonian path. The parent form takes connectedness of every single-vertex deletion directly. [ParentConnectivity.moderate](Graph189ParentConnectivity.lean) |
| κ≥3, k≥8, n≤3k+2 | A Hamiltonian path. [HighConnectivityQuarter.traceable_moderate](Graph189HighConnectivityQuarter.lean) |
| κ=3 or κ=4, k≥37 | A Hamiltonian path at every order. [Connectivity three](../global/three-cut-kernel/refinement/Graph189ThreeConnectivity.lean) and [connectivity four](../global/kappa4/Graph189FourConnectivityJoint.lean) |
| κ≥5, k≥26 | A Hamiltonian path at every order. [HighDegreeStructural.traceable](Graph189HighDegreeStructural.lean) and [independent integration](large-degree-proof.md) |

The exact moderate Lean obligation is proved. The remaining two-connected child begins at n≥3k+3 and k≥6. In particular the high-degree theorem at k≥26 leaves κ=2 in general, and κ=3,4 at k=26 through 36. The [paper proof](full-argument.md) addresses all orders. An unconditional parent Lean declaration and upstream verdict remain outstanding.

Replay with Lean 4.33.1, mathlib at 0df444a360eaa60ab8c11dca51a86af692955474 and formal-conjectures at 9097e2f90e66d2f6244209cb1c07f7120d17ec53. From the pinned mathlib project with its build cache installed, run the following command, providing absolute paths for the three checkout/build variables. The build directory should be dedicated to these pinned versions.

```sh
lake env python3 "$RESEARCH/research/graph189/full/direct/continuation/verify/replay-parent-ranges.py" \
  "$FORMAL_CONJECTURES" "$BUILD" Graph189FourOriginal Graph189ParentConnectivity \
  Graph189DegreeTwoOriginal Graph189HighDegreeStructural Graph189HighConnectivityQuarter
```

The replay builds each target independently against its declared imports. The [axiom audit](parent-range-axioms.txt) reports each main theorem and the SHA-256 of its source. The [degree-four proof](../verify/degree-four-low.md) and the [degree-two paper](degree-two-minimum-deletion.md) give the path constructions. The high-degree application credits @koolkao's accepted formalization of the linked-set theorem of Ma, Ning and Zhao. [Upstream source](https://github.com/lefttosolve2/open-math-agents/pull/7971)
