# Minimum cuts in the moderate order case

Let G satisfy the original even-distance hypothesis, let k be its second-smallest degree with multiplicity, and write n for its order and s for its vertex connectivity. Assume

    s ≥ 2,    n ≤ 3k+2,    k ≥ max(3s+3, 6s−5).

If G has no Hamiltonian path, it has a unique low vertex z of degree s, and its only minimum separating set is N(z). In particular making that specific z universal raises connectivity to at least s+1 and gives minimum degree at least k. This is a paper result for the moderate parent obligation. The fork also has a different paper route through exterior cycles for n≤4k and s≥3.

The path argument uses Ali's contact-rooted Fan/Dirac note of 28 November and the previously proved path gap at [the relevant checkpoint](https://github.com/ali-hamdan-007/open-math-agents/blob/928c13c86fb9a787b91451cca69d064147374ddc/research/graph189/full/direct/continuation/lowblock/all-near-spanning.md). A path missing at most ceil(k/2)+1 vertices suffices. All distances in the hypothesis are in G.

## Counting components

Put d=k−s and take any minimum cut S. Each component containing a vertex of degree at least k has at least d+1 vertices. There can be at most one additional component, a singleton consisting of the sole vertex of degree below k. Four high-containing components would give n≥s+4(d+1)>3k+2. Every member of S has a neighbor in every component, since deletion of fewer than s vertices leaves G connected.

## Two high-containing components

Let A and B be the two such components with |A|≤|B|. The optional singleton lies outside them. We have |A|≤2d−1 and |B|≤2k+1. The rooted path in B starts at a neighbor of some r∈S and contains at least min(|B|,2d+1) vertices. For completeness, attach an apex to the actual contacts in B. This graph is two-connected because deleting any B vertex leaves a surviving contact in every remaining piece. Temporarily also join the apex to the possible low vertex. Every non-apex vertex except possibly that low vertex has degree at least d+1, and the two exceptions are adjacent. Fan's distance-two degree theorem gives a cycle of order at least min(|B|+1,2d+2). If it passes through the apex, remove it and start at a genuine contact. If it avoids the apex, approach the cycle along a shortest path from the original apex and follow the cycle.

The smaller component has a spanning path from a neighbor of this particular r if it has no low vertex, by Dirac's Hamiltonian cycle theorem. If it contains a low vertex, remove that vertex and apply Dirac to the remaining graph (minimum degree ≥d−1, order ≤2d−2). When r touches only the low vertex, start there and enter the high cycle. At most one low vertex is lost, including the optional extra singleton.

If |B|≤2k, the total omitted is at most s+max(0,|B|−2d−1)≤3s−1. If |B|=2k+1, the order forces |A|=d+1 and rules out the extra singleton. Every high vertex of A is adjacent to all other vertices of A. Since at least one end of each pair in A is high, A is a clique, even if it contains the low vertex. It spans from any contact. Here the loss is at most (s−1)+2s=3s−1. Both bounds fit the gap allowance because ceil(k/2)≥3s−2.

## Three high-containing components

Each component has order at most k+s. Choose a wholly high middle component M. It has two different contact vertices, since a single contact would be a cut vertex of G. There are edges from distinct separator vertices r,t to distinct contacts of M. Indeed a bipartite edge set with at least two vertices incident on each shore contains two disjoint edges: if edges from r and t reach the same port, match an edge to a different port with whichever of those two edges avoids its other endpoint.

The middle has minimum internal degree at least d, so 2d≥|M|+1 gives a Hamilton path between the two chosen contacts by the Hamilton-connected form of Ore's theorem. At each end component the high core has minimum degree at least d−1 and 2(d−1)≥k+s+1. A Hamiltonian cycle of the core can be opened at a neighbor of the prescribed separator vertex. When its only contact is the low vertex, use it first and then enter the high core. The path uses r and t. At most s−2 separator vertices and the single possible low vertex are omitted.

## The exceptional cut

Only one high-containing component can therefore remain at any minimum cut of a counterexample. There must be another component, which must be the singleton low z. It has no neighbors outside S, while every member of S touches it. Hence S=N(z), independently of the choice of minimum cut. Since z belongs to no minimum separating set, the established completion-connectivity lemma applies, and every vertex other than z in the completion starts with degree at least k.

This shortcut removes cuts with two or three high-containing sides from the moderate-order formalization at these degree thresholds. It leaves the unique-neighborhood separator case and the lower degrees for that approach. The accompanying elementary Lean arithmetic is independent of the graph-theoretic routing. It does not certify the whole shortcut or either parent obligation.
