# Graph 189: a paper proof with finite arithmetic

The target is WrittenOnTheWallII.GraphConjecture189.conjecture189 in formal-conjectures at commit 9097e2f90e66. Let G be a finite connected simple graph on at least two vertices. Let k denote the second entry of the nondecreasing list of vertex degrees, including multiplicities. If every vertex has at most k other vertices at positive even distance, G admits a Hamiltonian path.

This is the full-target research argument. Its concluding exclusions have independent implementations. The complete argument has not been compiled as OMA.solution. In particular the standard graph-theoretic cycle and path results used in the papers, and the use of finite arithmetic to discharge graph configurations, carry proof obligations in Lean. The official verdict on reduction PR 18811 concerns a different statement.

## Reductions needed before the arithmetic

Assume a counterexample; let n, s and Δ be its order, vertex connectivity and maximum degree. Distances and even counts refer to the original graph unless an argument explicitly supplies a transfer. The single vertex whose degree can fall below k may be on either side of a separator or on the separator itself.

1. The cut-vertex and all separating-pair arguments, followed by the three-cut argument, exclude s≤3. See ../sep/unrestricted-two-cuts.md, ../sep/small-two-cuts.md, ../global/cut3/three-cut-all-degrees.md and ../verify/finite-three-cut-audit.md. The three-cut calculation at degrees 9–15 includes exact rational linear-arithmetic checks. Their inputs, decisions and independent replay are part of the research checkpoint.
2. For s=4 and k≥16 use ../verify/four-cut-three-components.md when deletion leaves at least three components. For two components the deep sides are handled by ../verify/four-cut-deep-all-sizes.md. In the shallow case use ../order/four-cut-shallow-common-anchor.md, ../global/cut4/no-singleton-large-side.md and ../order/four-cut-shallow-sole-nearest.md according to the contact pattern. Together with the earlier fixed-degree cases these exclude connectivity four at all degrees. See the frontier section for connectivity at most four for the small-degree dependencies.
3. All k≤25 and all 5s≥k are excluded by ../sep/cover/fifth-connectivity.md and its cited low-degree lemmas. Degree and order restrictions beyond these cases are proved in effective-cutoff.md. We may therefore assume 5≤s≤63, max(25,5s)<k<4s²+8s−2, Δ≤3k. These are necessary conditions on arbitrary counterexamples; the case split here does not assume a potential counterexample has a specific cut attaining its minimum degree.
4. See ../lowblock/finite-width-replay.md for the derivation of the finite order bounds, the explicit cut-incidence constraint at a possible low vertex, and the hypotheses of the lifted order estimate. The minimum-degree repair and cycle bound are in universal-minimum-order.md and ../global/arity/critical-removable-vertex.md. The shorter three-common-label order constant used by the arithmetic also uses the first paragraph of ../global/arity/finite-cover-credits.md.

## The two independent sets of inequalities

Choose x of maximum degree Δ, put e=Δ−k, and let C be the high vertices at distance three from x. A high vertex has degree ≥k. Along each geodesic x,i,j,y to y∈C the two induced wedges force lower bounds on the sum of their common-neighbor counts. Summing over targets consumes the even-distance allowances at first neighbors of x. An edge into the second layer costs a missing adjacency within the first layer because x has maximum degree. Counting these costs together with the even incidences between the two layers cancels the apparent extra allowance from the second layer. This gives w|C|≤kΔ, with w=ceil((2(n−2k)+ke)/(k+1)), and permits the stronger matched-wedge value specified in ../lowblock/active-column-width.md. Every used second-layer vertex has a high predecessor, even if the unique low vertex neighbors x. The diameter reduction gives |C|≥n−Δ−k−2.

Combining these constraints over every integer in the displayed initial domain gives 64 inclusive order intervals. This first calculation never tests whether a candidate graph has a spanning path.

| Connectivity s | Second-smallest degrees k | Intervals |
|---|---|---:|
| 5 | 58–81 | 24 |
| 6 | 88–109 | 22 |
| 7 | 124–141 | 18 |

Independently choose an optimized longest path in a putative counterexample. The path-gap and exterior lemmas give an omitted component containing a high vertex. Apply the contact-matching argument to the whole component if it is two-connected, and otherwise to a suitable endblock. The near Hamilton-connected case, the small endblock, and the large-block case are exhaustive as detailed in ../verify/final-exterior-audit.md and ../sep/cover/five-through-25.md. For each of the 64 intervals the lower orders required by those cases exceed the interval's upper end. The independent calculation uses only integer operations. The two sets of necessary conditions have no common instance. This contradiction gives traceability.

## Reproduction

From the continuation directory:

```sh
python3 lowblock/finite_width_replay.py > /tmp/graph189-orders.tsv
cmp /tmp/graph189-orders.tsv lowblock/finite_width_checked.tsv
python3 verify/exterior-simpler/independent_core.py /tmp/graph189-orders.tsv /tmp/graph189-orders.tsv
```

The same input is passed twice because the verifier can intersect two data sets. Here that preserves every row. Run Python with assertions enabled. The expected final line is `total 64`: every interval was tested, and a surviving exterior configuration would raise an assertion. The committed input's SHA-256 is `dcf24f7a3072bca5ffab575eb89fcfcc756ddf8a00576315bce7b6df5e883f52`. The independent certificate under ../sep/cover/final82/ also treats a broader 82-row enclosure.
