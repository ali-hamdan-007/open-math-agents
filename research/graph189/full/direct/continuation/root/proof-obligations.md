# Parent formalization dependencies

The conditional root theorem and its two residual propositions are in parent/parent-assembly.md. All items here refer to formal proof in the original graph setting. A theorem marked absent in this map may already have a paper proof.

| Part of contradiction | Lean checkpoint | Remaining dependency |
|---|---|---|
| All connected graphs through order 2k+2, and graphs with a cut vertex | Original R2 plus cut-vertex proof in the conditional parent assembly | Unconditional proof of the two-connected branch |
| Bounding the maximum degree and counting third neighbors | order/Graph189MaximumDegree.lean and verify/Graph189RootWidth.lean | Use the actual order inequalities with the lower bounds at a minimum cut |
| Order and connectivity cutoff for the alternative 102-band route | global/arity/final/Graph189InfiniteTail.lean and verify/Graph189WidthInterval.lean | Derive every cut-order input from graph structure; certify that the generator includes every resulting finite parameter tuple |
| Two populations at a minimum separator | order/Graph189CutSides.lean and order/Graph189MinimumCut.lean | Count private, common and complementary supports and complete the change-of-separator contradiction |
| Terminal scalar inequalities for the 102 bands | global/arity/final/Graph189FiniteDomain.lean and Graph189TerminalQuotas.lean | Supply the graph-derived premises for the exhaustive bands |
| Alternative 64-band exterior-path argument | root/full-argument.md and sep/cover/final82/ | Formal path gap, block/attachment and inherited-distance arguments, plus exact finite-domain coverage, are needed for this route |

The previous low-connectivity results, the long-cycle order theorem and the critical-connectivity input enter before the finite contradiction. Proving the 102-band route needs only the basic rounded root width. The 64-band route uses the stronger matched-wedge bound. A passing terminal table establishes all entries in its literal list; membership of a counterexample's parameters in that list is a distinct theorem.
