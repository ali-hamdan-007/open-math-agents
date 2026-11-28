# Arbitrary induced patterns on low-degree vertices in the large-order regime

Let k be the second-smallest degree, and let e(v) count vertices at positive even distance from v. For every nonempty finite simple graph J there exist 2-connected Hamiltonian graphs G containing an induced copy of J, with all of the following properties.

* Every vertex v satisfies e(v) ≤ k.
* The excess |V(G)| − 3k can be arbitrarily large.
* Every vertex of the chosen J has degree strictly below (|V(G)|−1)/2.
* Every nonedge of G has degree sum strictly below |V(G)|−1.

In particular, every bond in the usual traceability degree-sum closure is already present. The cone over G also has stationary Hamiltonian degree-sum closure, since an original nonedge gains two in degree sum while the order gains one. The lightness of the planted vertices persists in the cone at its Hamiltonicity threshold.

## Construction and proof

Write b = |V(J)|, fix t ≥ b, and let c = (2,2,3,4,4,3,2). Replace vertex i of the 7-cycle by a clique V_i of size b+t c_i, joining consecutive cliques completely, with no other edges between different cliques. Choose b vertices P of V_1 and delete internal edges of P until G[P] is isomorphic to J.

The seven degrees before edge deletions are 3b−1 plus t times the respective coefficients (6,7,9,11,11,9,7). Their minimum 6t+3b−1 is attained on all of V_0. Only vertices in P can lose degree. Their maximum loss b−1 is at most t, so the minimum of the degree sequence stays unchanged and is attained at least twice. Thus k=6t+3b−1. The order n is 20t+7b, and n−3k−2 = 2t−2b+1.

Originally e(v) is the sum of the sizes of the two cliques at cyclic distance two from its part. Its seven values are 2b plus t times (6,6,6,5,5,6,6). Changing edges of P only changes distances of the deleted pairs. A vertex pair in distinct parts still has a shortest path following a shortest segment of the 7-cycle with one vertex per visited part. A missing pair in P now has distance two through an ordinary vertex of V_1. As a result any single e(v) increases by at most b−1, giving e(v) ≤ 6t+2b+b−1 = k.

Each vertex in P has degree at most 7t+3b−1, with twice this bound strictly below n−1. For any original nonedge, the two part indices are nonconsecutive and distinct. Inspecting the seven degree coefficients shows that the largest sum over such pairs is 20. Thus its degree sum is at most 20t+6b−2 < n−1. All new nonedges lie within P and have already been bounded. No edge can be added by the traceability closure at threshold n−1. In the cone, the degree sum of each nonedge is at most n after adding two to it, which is below the new graph order n+1.

A Hamiltonian cycle follows the parts in cyclic order. Within V_1, interleave the b special vertices with b ordinary vertices. Place the other ordinary vertices afterward. The other parts are cliques with arbitrary internal order. This gives a spanning cycle and hence 2-connectivity. In fact deleting fewer than 2t vertices leaves an ordinary vertex in each part, so the vertex connectivity also tends to infinity.

## Consequences

Any proper hereditary class of finite simple graphs excludes some fixed graph J as an induced subgraph. Thus the qualifying large-order graphs, even after taking their traceability closures, are not all members of any such class. More generally, given any fixed induced pattern J with nonedges, no universal consequence can demand a heavy vertex, a heavy distance-two pair in the Fan sense, or an Ore-heavy nonadjacent vertex pair in every copy of J. In the planted copy of J, all vertices and all pairs are light even under the weaker traceability threshold. These are obstructions to automatically satisfying sufficient conditions. They leave the spanning-path conjecture open.

For the claw specifically, this also excludes the line-graph-homeomorphism route on the unconstrained reduced graphs. Pick J to be a claw. Every vertex of G has degree ≥3, so any simple graph homeomorphic to G is obtained by subdividing its edges. Every subdivision retains a claw centered at the same branch vertex: take the nearest vertex to it along each of the three selected edges. These are still pairwise nonadjacent. A line graph cannot contain such a claw, since three edges each incident with the central edge must include two meeting the same endpoint.

Subdivision is not a generic equivalence for traceability of a 2-connected graph. Subdividing every edge of K4 once gives a bipartite 2-connected graph with parts of sizes 4 and 6 and no spanning path. The metric hypothesis also varies within a homeomorphism class: C3 has e(v)=0 and C8 has e(v)=3 while both have k=2.

## Smaller claw example

For n=27, use (3,3,4,5,5,4,3) for the seven clique sizes and delete just the edge xy between two vertices of V_3. A vertex of V_2 centers a claw with leaves x,y and any vertex z of V_1. The degrees are respectively 12,12,9. The maximum positive-even count is 8 and k=8. The maximum degree sum on any nonedge is 24, below n−1 = 26.

The elementary BFS checker in claw_obstruction.py verifies these values and the individual Hamiltonian cycle, then checks the related family with b=2 and one missing edge in V_1 for 2 ≤ t ≤ 12. The arbitrary-J argument is by the uniform proof above.
