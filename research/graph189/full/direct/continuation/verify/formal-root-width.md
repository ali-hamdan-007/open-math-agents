# The rounded width at a maximum-degree vertex

Under the registered Graph 189 hypotheses, write n for the order, k for the second-smallest degree and d for the maximum degree. Set w = ⌈max(0, 2(n−2k)+k(d−k))/(k+1)⌉. Then

    w · max(0,n−d−k−2) ≤ kd.

The Lean declaration Graph189RootWidth.root_width_bound takes connectedness and exactly the original bound on the maximum of distEven. The graph is finite and simple, with at least two vertices. Neither a path obstruction nor a connectivity lower bound is an argument.

Graph189HighThirdLayer.card_highThird_at_max proves the lower bound on the number of high vertices three steps from a maximum-degree root. The first neighborhood, the even-distance set containing the root, this high third layer, and a single chosen minimum-degree vertex cover all vertices. The R1 diameter bound rules out larger distances and the R1 distance-five endpoint theorem rules out distance five between two high vertices.

Graph189RetainedWidth.geodesic_degree_width bounds the two common-neighbor incidences of every three-edge geodesic. Graph189ColumnCancel.full_column_cancellation charges their sum over all high third-layer endpoints against the first-layer capacity. Graph189RootWidth.root_width_bound derives both the rounded charge and the actual third-layer count with the original graph invariants. Each source passed lean -j1 -DwarningAsError=true using Lean 4.33.1 and formal-conjectures 9097e2f90e66d. Its printed axioms are propext, Classical.choice and Quot.sound.

The rounded width feeds the 102-band scalar argument. The separate 64-band argument also uses the stronger matched-wedge width. Proofs of the unrestricted Hamiltonian-path implication require additional graph lemmas.

Source hashes for the main bridge and graph inputs follow.

| File | SHA-256 |
| --- | --- |
| verify/Graph189RootWidth.lean | 7ea6d8761ad6b1306ee5970109e480644e819f5c1cdb7a4802814d37c68d0138 |
| verify/Graph189HighThirdLayer.lean | 3b1b3894d0c83c1b21cde07ad3c1f5439f9055a747cbc97ef0ed766c69c54d67 |
| verify/Graph189RetainedWidth.lean | f2d8012bdb0badb822df91e374e3c018d6603a012acc1dbdba279001391919ab |
| lowblock/Graph189ColumnCancel.lean | e7afc5120d5aff8034737c2130a181e63110c5232e10ee5b7685062fe2258a10 |
| verify/Graph189R1Metric.lean | 2c8bb5f89b350137554d190a4e83b83c9610f2a2a3de2f56c68ae607f0f5b212 |

Set OMA_FC to the pinned checkout and run verify/replay-root-width.sh to rebuild the six source modules. The session's separate successful builds are recorded in verify/high-third.log, verify/retained-width.log, lowblock/column-check.log and verify/root-width.log.

## The continuous interval test

Graph189WidthInterval.necessary_interval specializes the rounded bound, the maximum-degree ceiling and the rooted Hamilton-path theorem to arbitrary counterexamples satisfying the original graph hypotheses. For n>4k+2, set L=k+max(0,⌈(n−3k−1)/k⌉) and F(d)=(n−d−k−2)(2(n−2k)+k(d−k))−(k+1)kd. The theorem gives L≤3k and min(F(L),F(3k))≤0. Its integer proof uses concavity to eliminate the unknown actual maximum degree, with exact rounding and casts. Pinned Werror compilation printed the three standard axioms; source SHA-256 13ed672e6d039fe7a9c7ea78b04f88cd6540ed49700bcf75eba7b19596cde7fd.

Graph189WidthInterval.replay_widthPossible then imports the actual executable's definition and proves that its Boolean result is true for every counterexample to the registered conjecture. The adapter passed the same pinned kernel, with just the three standard axioms. Its SHA-256 is 6786547e2aa14d5865795d060cb7132d440e55c6a091ecd87af36e695a17bcfd. Use verify/replay-root-width.sh --replay-test for this full chain. The individual prints are in verify/width-interval.log and verify/width-replay.log.
