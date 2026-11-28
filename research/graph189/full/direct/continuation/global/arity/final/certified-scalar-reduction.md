# Kernel-certified scalar reduction for Graph 189

The final scalar theorem, Graph189ScalarConclusion.terminal_band, takes arbitrary integer n, k, s, maximum-degree excess e, root width w, and effective degree deficit d. Assuming s≥5, k≥26 and the graph bounds listed below, it proves s≤8 and produces a valid terminal band whose lower order is at most n. The theorem has no finite parameter bound as an input. All finite comparisons used in this proof run by ordinary kernel reduction.

## Inputs and interpretation

* The basic connectivity restriction 3s<k; see ../../../sep/cover/third-connectivity.md.
* The maximum-degree bound 0≤e≤2k, the rooted Ore inequality n≤3k+1+ke, and the cancelled root-width estimates 2(n−2k)+ke≤(k+1)w and w(n−2k−e−2)≤k(k+e). The original-graph width and rooted inequalities are formalized in the adjoining graph modules.
* The unconditional lower order n≥(s+1)(k−s+2)−1, the cut-population upper estimate (n−2k−1)(k−s)≤sk², and the two common-support upper orders when k>6(s−1). See ../../../root/universal-minimum-order.md, ../arbitrary-cut-high-order.md and ../three-common-labels.md. Graph189CutPopulationOrder.cut_order derives the cut-population estimate from the genuine even-distance capacities and separator witnesses.
* Choose d=0 when the full lower-order lift applies. A positive d belongs to a genuine low on a minimum cut. Its witnesses satisfy r≤s, d≤r−1, 0≤x≤y, x+y=n−s, x(y−k)≤sk², kd≤2k+(k+1)r−n, and the mixed-debit inequality (r−1)(k−s+1)≤(s+1)k−n+x+s+r(e+s−1). These inequalities are the ones proved in ../../../lowblock/finite-cross-cut-low-degree.md; the graph-facing mixed debit is in ../../../order/Graph189MixedDebit.lean.
* When 3s<2(k−d−1), 2s≤k−2d−2 and 4n<k(k−1), the lifted order n≥(s+2)(k−d−s+1)−1 applies. The independent-exterior alternative is retained by this condition. See ../critical-removable-vertex.md and ../three-common-labels.md.

## Elimination and the remaining 113 bands

Graph189EightCutoff.connectivity_le_eight eliminates all larger connectivities. It joins the infinite cutoff, 286 kernel-certified width windows, the high-degree alternative and the two connectivity-nine estimates. Its proof is described in compressed-width-coverage.md.

At 5≤s≤8, first apply the unconditional order. If k≥4s, also apply the smaller of the robust lower order (s+2)(k−2s+2)−1 and ceil(k(k−1)/4). Call the resulting lower bound L. For a positive deficit the low wedge alone gives kd≤2k+(k+1)s−L. Therefore a valid upper bound on d throughout the entire pair (s,k) is

    D=max(0,min(s−1,floor((2k+(k+1)s−L)/k))).

At s=5 and 46≤k≤58 the mixed debit excludes a positive deficit. The complete scalar theorem invokes ../../../verify/Graph189FiveCutDebit.lean there and uses D=0. The lower order is then raised, when the lift conditions at D permit it, to the smaller of (s+2)(k−D−s+1)−1 and ceil(k(k−1)/4). Call the result L′. Graph189SmallWindowCover.lower_le proves n≥L′ throughout the whole pair.

The bound k<4s²+8s−2 gives k<318. For every remaining s and k, Graph189SmallWindowCover.all_pairs verifies that either L′ already violates an order bound, the continuous maximum-root width at L′ is impossible, or the band with lower endpoint L′ has valid terminal inequalities. It uses the linear width and the ordinary rooted Ore lower bound alone. There is no search over n, e or d for a fixed pair. The 113 recorded positive-population caps comprise 31 degree values at s=5, 33 at s=6, 29 at s=7 and 20 at s=8. The table terminal-113.tsv gives their k, L′ and population caps.

Graph189ValidBand.consequences applies each resulting band to arbitrary cut populations. It proves the upper bound on the smaller high population, the strict lower bound Y>sk on the larger one, the second-cut orientation cap, and the contradictions to the all-private and one/two-common residual-singleton bounds. The associated graph arguments forcing one of the support obstructions or a second separator are in finite-scalar-theorem.md and its cited papers.

## Replay

From this directory run

    bash replay-certified.sh PATH_TO_PINNED_MATHLIB_PROJECT

The wrapper builds the eleven source modules in a fresh output directory using Lean 4.33.1 with warnings treated as errors. An optional second argument selects the output directory. All dependencies of the scalar calculation are local sources plus Mathlib. The checked assertion is an ordinary Lean theorem, with the standard axioms propext, Classical.choice and Quot.sound. The older independent Python/Lean-executable 102-band replay is an alternative numerical route.

This file documents the scalar implication. The full Graph 189 statement additionally requires that the original graph supply the stated order and effective-deficit inputs, and that the geometric terminal alternative hold.
