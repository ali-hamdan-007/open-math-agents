# Bipartite case of Written on the Wall II, Conjecture 189

Ermelinda DeLaViña’s [Conjecture 189](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) asks whether every finite connected simple graph of order at least two has a Hamiltonian path if, for every vertex, the number of vertices at even distance from it is at most 1 + σ(G), where σ(G) is the second-smallest degree. Distance zero counts.

The bipartite case is proved in Lean. Import `Graph189BipartiteFull` and use `Graph189Bipartite.hamiltonian_bipartite`. The theorem uses the pinned Formal Conjectures definitions of `distEven` and `secondSmallestDegree` and adds only `G.IsBipartite` to the original statement. The general case for nonbipartite graphs remains outside this result.

## Proof

Let X and Y be the color classes, with 1 ≤ |X| ≤ |Y|. Along every walk, the color flips at each step. By connectivity, the even-distance vertices of a vertex are exactly its color class. Thus σ(G) ≥ |Y| − 1. At most one vertex has degree below σ(G). If |Y| ≥ 2, select a vertex of Y whose degree is at least σ(G). Its neighbors belong to X, so |X| ≥ |Y| − 1.

**Unequal parts.** Here |Y| = |X| + 1. Except possibly for one vertex, each vertex of Y is adjacent to every vertex of X. Start at the exceptional vertex if one exists, using any of its neighbors as the second vertex. Then alternate between the two parts until all vertices have appeared. Lean proves this with induction on the two finite sets of remaining vertices.

**Equal parts of size m ≥ 4.** By exchanging the colors if needed, choose a vertex z in X so that every other vertex has degree at least σ(G). Each vertex other than z misses at most one edge to the opposite color class. After removing z, the missing cross edges therefore form a matching. Extend that matching to an injection from X ∖ {z} to Y. For k = m − 1, index the vertices as x₀, …, xₖ₋₁ and y₀, …, yₖ so that every missing cross edge has the form xᵢ–yᵢ with i < k. The extra right vertex yₖ is adjacent to every xᵢ.

Take the path starting at y₀ whose successive blocks are (yᵢ, x₍ᵢ₊₂ mod k₎) for i from 0 to k − 1, then append yₖ. The two consecutive cross edges involving each interior x have distinct indices because k ≥ 3. A simultaneous permutation of the two matched index sets lets any yᵢ with i < k start the path. Reversal lets yₖ start it. Choose a starting vertex adjacent to z, and prepend z.

**Small equal parts.** When m = 1, connectivity supplies the edge. When m = 2, connectivity gives a vertex u with degree two, hence adjacent to both vertices of the opposite color. The other vertex v of u’s color has a neighbor x. With y the other opposite vertex, the path is y–u–x–v. When m = 3, connectivity gives every vertex a neighbor, and all but at most one vertex have at least two neighbors because σ(G) ≥ 2. Lean checks all 512 Boolean adjacency tables for the two labeled triples under these conditions. The certificate uses `decide +kernel`. The proof transports the resulting alternating path to the original graph and checks distinctness and full length.

## Verification and attribution

Run `./check-189.sh` against the pinned toolchain and focused dependency cache. The audit for the final theorem lists `propext`, `Classical.choice`, and `Quot.sound`. Every step above is covered by the Lean proof.

The second-smallest-degree order-statistic lemma is adapted from the [OMA R1 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2971) for `WrittenOnTheWallII.GraphConjecture189.conjecture189`. The indexed path proof reuses the list-chain assembly lemma from the separate Graph 199 development.
