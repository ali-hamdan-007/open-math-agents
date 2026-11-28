# Graph-facing terminal reduction for Graph 189

Let G be a finite connected simple graph with at least two vertices. Write s for the vertex connectivity, k for the second-smallest degree and n for the number of vertices. Assume each vertex has at most k other vertices at positive even distance and that G has no Hamiltonian path. The domain reduction addresses s≥5, k≥26 and k>3s.

Define d as k minus the minimum degree if a genuine low vertex belongs to a minimum separating vertex set. In all other cases, set d=0. This definition belongs to G and does not depend on a selected separator or an arbitrarily chosen integer witness.

## Remaining structural inputs

| Source of order information | Inequality |
|---|---|
| Baseline long-cycle bound | n≥(s+1)(k−s+2)−1 |
| First high-order cut bound when k>6(s−1) | 2n<(2s+3)k+4s+4 |
| Second high-order cut bound when k>6(s−1) | (s−2)(n−2s−3)<((s+1)(s−2)+3)k |
| Deficit-sensitive long-cycle lift when 3s<2(k−d−1), 2s≤k−2d−2 and 4n<k(k−1) | n≥(s+2)(k−d−s+1)−1 |

The terminal_band theorem uses these four inputs. The stronger exists_valid_band conclusion needs only the first and last. If either high-order upper fails, Graph189SyntheticBand.high_order constructs a band at order n with cap k+⌊k/(s−1)⌋. Otherwise the finite-domain theorem constructs one. In both branches its connectivity and degree parameters agree with G, its lower bound applies to n, and its validity test passes. All degree, width, population, and mixed-cut inputs are derived directly from G.

## Conclusion

The graph-facing theorem gives s≤8. The certified test Graph189FiniteDomain.valid is true for the pair’s band, and its lower order bound applies to n. The separate, previously checked finite support table for the cap records the four ranges below. The main theorem and the cut contradiction operate directly on a valid band.

| s | k |
|---|---|
| 5 | 51–81 |
| 6 | 77–109 |
| 7 | 113–141 |
| 8 | 158–177 |

The reflected table has 113 supported pairs. The separate degree_ranges lemma applies when the smaller high population is positive and k<318. The graph-facing existence theorem uses validity directly, including for synthetic bands outside this table.

## Graph input proofs

* Graph189ActualScalarWidth.lean takes the actual maximum degree and the rounded maximum-root width. It proves the two width inequalities, the maximum-degree constraint and the rooted order upper from the even-distance cap and nontraceability.
* Graph189EffectiveDeficit.lean takes an actual minimum cut containing the low vertex when d>0. It orients its sides by size and uses one pair of opposite contacts for all three deficit inequalities. The two side populations sum exactly to n−s.
* Graph189GraphPopulation.lean proves (n−2k−1)(k−s)≤sk². If a degree is at most s, the layer count rooted there suffices. Otherwise each side of the minimum cut contains a high vertex and the genuine cross-population bound gives the inequality.
* Graph189TerminalDegrees.lean checks the finite support table used for the displayed degree ranges. The primary graph-facing proof has no dependency on it.

The checked scalar implication and finite arithmetic appear in certified-scalar-reduction.md. The graph-only replay is replay-graph-bridge.sh. It recompiles the graph-facing source modules in a clean directory and imports their exported theorem using the pinned Lean compiler with warnings promoted to errors.
