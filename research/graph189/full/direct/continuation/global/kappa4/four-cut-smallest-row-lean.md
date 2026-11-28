# Lean draft for the degree-18 smallest-population row

Graph189FourSmallestRow.lean is a source draft for the exact replay family $k=18$, $x=14$, $y=70$, under the original graph and its given minimum four-cut. It uses a scalar projection of the selected mask row. It needs no Z3 verdict or parsed solver proof.

The projected natural-number variables are the B-port count $p$, the B nonports avoiding the low vertex's support in their nearest-label masks $q$, the B nonports meeting that support $r$, and the number $m$ of anchors the low vertex misses. In the absence of an eligible private port, the graph gives
$$p+q+r=y,\quad p\le k,\quad q+m\le k,\quad q+2r+m\le4k,\quad m\ge1.$$
The closed Boolean check is $7k<2y+2$. The declaration checked_18_70 uses ordinary decide over these numerals. The soundness step derives the opposite inequality with omega from the displayed graph inequalities. The graph projection constructs these sets and quotas explicitly.

The module imports three existing units:

- Graph189FullLabelExit for closed_size and tight_full. Its transitive Graph189PrivatePredecessor provides nonport_full_neighbor and high_private, and Graph189PortDifference.cross_two provides the cross-cut distance-two witness.
- Graph189PositiveEvenCut for separator_distance, high_distance_four, four_layer_quota, even_others_card, and mem_even_others. The draft derives that a high B nonport has a nearest anchor at distance two, using the exact $x=k-4$ and a genuine anchor neighbor of the low vertex. The existence of this low anchor neighbor follows from the checked two-root cover if the low vertex were a nonport.
- Graph189TwoRootRecut for Graph189FourCut.private_recut. Its transitive minimum-cut package supplies Graph189CutSides.connected_after_smaller_deletion.

The degree18_row_14_70 theorem returns an actual high B port with singleton anchor support and at least $k-3$ opposite contacts at that anchor. The exclude_degree18_row_14_70 theorem then returns a contradiction with the outer uniform-support property at every reoriented minimum cut. The row's public hypotheses expose the original connected graph, the pointwise parity quota, the exact populations, and high anchors. The final wrapper exposes the uniform-support conclusion needed from the remaining rows. It infers the recut's order room from the two disjoint populations.

The source still needs a pinned Lean compile, warnings-as-errors review and axiom inspection. This single reflected scalar row leaves separate the other finite mask queries, high-anchor reduction for the entire degree range, and the outer uniform-support argument.
