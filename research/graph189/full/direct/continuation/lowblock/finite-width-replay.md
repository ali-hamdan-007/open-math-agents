# Standalone scalar replay for the final 64 intervals

From this directory run

    python3 finite_width_replay.py > finite_width_checked.tsv

Python 3.8 or newer and its standard library suffice. The calculation never calls another graph-enumeration program. The four space-separated integers in each row are s, k, the least feasible n, and the greatest feasible n. The interval encloses every possible order. The published table has 64 rows, distributed 24, 22 and 18 at connectivities 5, 6 and 7. The larger cutoffs and the conditional degree-lifting parameters are evaluated afresh.

## Mathematical inputs

* The initial parameter bounds 5≤s≤63, k>max(25,5s), k<4s²+8s−2 and Δ≤3k come from ../root/effective-cutoff.md and the small-connectivity, k≤25 and one-fifth-connectivity results cited there. The bound for k at s=5 follows from the strict (s+3/2) and critical lower orders, as in ../global/arity/critical-removable-vertex.md and ../global/arity/three-common-labels.md: k≤137 at s=5.
* The unconditional lower n≥(s+1)(k−s+2)−1 is in ../root/universal-minimum-order.md. For the upper limits use geodesic-width-and-order.md, ../root/nontrivial-cut-sides-and-exterior-cycle.md, ../global/arity/arbitrary-cut-high-order.md, and the first paragraph of ../global/arity/finite-cover-credits.md sharpening the order constants from ../global/arity/three-common-labels.md. The last two upper bounds are used only at k>6(s−1).
* At a maximum-degree root put e=Δ−k. The lower bound for e combines the rooted Ore test n≤3k+1+(k−2)e from ../verify/wedge-order-refinement.md and the concave test n≤3k+1+e(k−e−1) when 2e≤k−1 from ../verify/wedge-penultimate-matching.md. The upper e≤2k is the maximum degree bound above.
* The two integer minimum-width lower bounds and the upper w(n−2k−e−2)≤k(k+e) are in active-column-width.md. They hold with an arbitrary low degree. The mixed low-cut bound on its possible deficit used by low_cut_allows, including the all-high and no-low-on-any-minimum-cut alternatives, is in finite-cross-cut-low-degree.md. That paper invokes the finite cut-population product bound in ../root/minimum-cut-populations.md and the critical-removable-vertex and exterior-cycle lift in ../global/arity/critical-removable-vertex.md. The numerical replay never requires its supplementary uniform s≥100 argument.
* The final exterior exclusion of all 64 rows has a separately written checker in ../verify/exterior-simpler/independent_core.py, as well as the exterior group's own certificate.

## Integer bounds and search

For x≤(n−s)/2 the size condition is x(n−s−k−x)≤sk². The midpoint is checked first; if it fails, concavity makes the feasible domain a prefix. The mixed low deficit is maximized over all common-label counts 1 through s for the specific candidate e and n. If the sufficient conditions for the critical lift fail, that n is retained at this stage.

Before scanning specific orders the replay also bounds the smaller side by X(X−k)≤sk², valid since Y≥X. At the universal lower order it takes the greatest feasible excess for the relaxed inequality, and upper-bounds the shared-label and low deficit on all later orders. The resulting uniform lifted lower bound follows because increasing order can only decrease these upper bounds.

The continuous width relaxation has difference
    F(e)=(n−2k−e−2)(2(n−2k)+ke)−(k+1)k(k+e).
It is concave in e, so no excess lying between two rejected endpoints can work. At s≥5, k>5s the lower order n≥(s+1)(k−s+2)−1 exceeds 4k+2. Hence the first factor n−2k−e−2 is positive throughout e≤2k. For a fixed excess the width-only filters become weaker upon lowering n, since both required widths and this nonnegative factor are nondecreasing in n. The lower limit on e is likewise nondecreasing in n. This proves the initial-interval property used to bisect the upper order. The extra cut-deficit condition is evaluated separately on successive integer orders from either end, without assuming any monotonicity for it.

In the discrete matched-width loop, K=D−2−e≥0 is required. The exact packing at K≤k−3 is f(⌊K/2⌋)+f(⌈K/2⌉), where f(t)=t(k−t−1); above that range the loop simply stops and imposes no further matched-width restrictions. Each printed interval is therefore a safe enclosure.
