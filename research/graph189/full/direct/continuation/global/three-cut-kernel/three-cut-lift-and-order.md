# A three-cut comparison at the lifted order

Write s for vertex connectivity, k for the second-smallest degree, n for order and δ for minimum degree. All distance counts use the original graph.

## Lower bound from a nontraceable minimum deletion

Assume G and G−z are nontraceable for a minimum-degree vertex z. Consider s = 3 with k ≥ 26, or s = 4 with k ≥ 30. If every minimum separator avoids z, making z universal raises connectivity to at least s+1 and minimum degree to at least k. The minimum-completion linked sets and the accepted linked-set theorem at index s+1 give

    n ≥ (s+2)(k−s+1)−1.

If a minimum separator contains z, the anchor-degree bound gives δ ≥ k+1−s. The critical-completion theorem supplies a universal completion of connectivity at least s+1 and minimum degree at least δ. Calling Graph189CompletionLinked.critical with its independent parameter 5 gives a linked witness at index 6, since k+12 ≤ 2δ. The same set and paths witness every smaller index. Consequently n ≥ (s+2)(δ−s+1)−1. This gives the desired bound when δ ≥ k.

Otherwise put d = k−δ ≥ 1. The low-cut debit gives n+kd ≤ 2k+(k+1)r for some 1 ≤ r ≤ s. Combining it with the critical lower bound gives

    (k−s−2)d ≤ s²+2s−1.

At s = 3 the right side is 14, contradicting k ≥ 26. At s = 4 it is 23, contradicting k ≥ 30. Thus the full lower bound holds regardless of which minimum separators contain z.

## Upper bound at connectivity three

Orient a minimum three-cut by its smaller high population x. Write y for the other high population. The graph counts give x+y ≥ n−4 and xy ≤ kx+3k². At k ≥ 38 and n ≥ 5k−11 the following arithmetic facts hold:

    y > 3k,    3y > 9k−15+x,    and, if x ≤ k, 2y > 6k+x.

Indeed, x² ≤ kx+3k² implies 13x ≤ 30k. Hence x ≤ 3k−27 at k ≥ 39. At k = 38 a violation would mean x = 87 and y ≥ 88, contradicting the product bound. If x ≥ k+12, then (x−k−12)(3k−27−x) ≥ 0. From x+y ≥ 5k−15 we obtain x(y−k) ≥ (k+12)(3k−27) > 3k². Thus x ≤ k+11, proving the first two inequalities. For the third use x ≤ k and x+y ≥ 5k−15.

If there is no separator label common to all small-side high vertices, the singleton-or-two-missing classification forces all high supports to have size at most one. The private quota gives 3y ≤ 9k−15+x, impossible. A contact opposite a common label sees all x small-side high vertices at distance two, so x ≤ k. If no high port is full, every high support contains at most one label outside this common label. The residual-singleton quota gives 2y ≤ 6k+x, also impossible. Consequently there is both a full high port and a common label. Since y > 3k, the one-new-label theorem against the full row gives every small-side high port at least two labels. This holds for every oriented minimum cut.

Graph189FullLabelExit.full_exit supplies a high private port on the opposite side with the capacity needed for a new cut. Graph189FourCut.private_recut applies at any separator size and puts a high port meeting just one label on the small side of another minimum cut. Its order hypothesis n ≥ 4k+s+1 holds here. This contradicts the preceding two-label conclusion.

At s = 3, k ≥ 38 and every graph order, the two bounds exclude a counterexample with a nontraceable minimum deletion. In the other case Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion constructs a Hamiltonian path in the original graph. Together they prove Graph189ThreeConnectivity.traceable under the original connectedness and even-distance hypotheses. The lower bound, upper bound, both alternatives and the graph-facing wrapper passed pinned Lean 4.33.1 locally with propext, Classical.choice and Quot.sound. The logs are lift.log, joint-corrected.log and three-connectivity.log. This is a family of the parent conjecture.
