# Triangle-free case of Written on the Wall II, Conjecture 189

Every triangle-free, nonbipartite graph satisfying DeLaViña’s degree condition is an odd cycle. The checked theorem `Graph189TriangleFree.hamiltonian` proves the Hamiltonian-path consequence for every triangle-free graph. Lean constructs a shortest odd closed walk, checks that its cyclic indices are distinct, and proves the cycle geometry by ruling out shorter detours of the same parity. This includes the earlier checked result for graphs with no triangles or four-cycles.

Write s for the second-smallest degree and C for a shortest odd cycle, of odd length m ≥ 5. Such a cycle exists in a nonbipartite graph. It is induced because a chord splits it into two shorter cycles, one odd. Every vertex of C has exactly two neighbors in C and at least two vertices at distance two in C. Including distance zero, each vertex of C therefore contributes at least three even-distance vertices inside C, so s ≥ 2.

Let x be outside C. For two distinct neighbors of x on C, the two arcs between them have opposite parity. The odd arc and the two edges to x form an odd cycle. This cycle has length at least m, so the even arc has length exactly two. Thus x has at most two neighbors on C. Indeed, fix one such neighbor. The only two possible additional neighbors are its two cyclic offsets ±2. Between those possible neighbors the even arc has length four, so both cannot be neighbors of x.

If x has one neighbor on C, the two cyclic neighbors of that vertex on C are at distance two from x. If x has two neighbors on C, the two pairs of cyclic neighbors have exactly one vertex in common, giving three vertices of C at distance two from x. In both cases triangle-freeness rules out an edge from x to any counted vertex. Therefore the number of distance-two incidences from x to C is at least three halves the number of edge incidences from x to C. This remains true when x has no neighbors on C.

There are at least m − 1 cycle vertices of degree at least s. Each contributes at least s − 2 edge incidences to the complement of C. Each cycle vertex contributes at most s − 2 distance-two incidences to the complement of C, because its total even-distance count is at most 1 + s and at least three of those vertices are in C. Double count the two kinds of incidences to obtain

$$
m(s-2) \ge \frac32(m-1)(s-2).
$$

Since m ≥ 5, the coefficient on the right is strictly larger than m. This forces s = 2. The distance-two incidence count from C to its complement is then zero, so no edge joins C to its complement. Connectivity forces C to span the graph. As C is induced, the graph is the odd cycle itself. Removing one cycle edge gives a Hamiltonian path.

The kernel-checked bipartite case covers all other triangle-free graphs under the conjecture's hypotheses. The diameter-three reduction now leaves two cases containing a triangle, distinguished by whether the minimum degree is at most two or at least three. Explicit graphs satisfy every inherited premise in both cases. Source: [Written on the Wall II, Conjecture 189](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).

Run `./check-189.sh` for the pinned build. Its axiom audit for the triangle-free theorem lists `propext`, `Classical.choice`, and `Quot.sound`.
