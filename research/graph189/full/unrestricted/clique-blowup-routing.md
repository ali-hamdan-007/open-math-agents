# Exact asymmetric clique-blowup routing and restrictions

For a connected simple template H with at least two vertices, assign a positive integer size w_v to each vertex. Replace v by a clique of that size and put all edges between two such cliques if and only if the corresponding template vertices are adjacent. Write H[w] for the result. Costs and adjacency in this note refer to H unless explicitly indicated.

## Exact traceability test

**Proposition.** H[w] has a spanning path if and only if there is a connected spanning multigraph on H whose edge multiplicities belong to {0,1,2}, which has exactly two odd-degree vertices and for each v satisfies
\[
 \frac{\deg_M(v)+\mathbf 1_{\deg_M(v)\ {\rm odd}}}{2}\le w_v.
\]

Given a spanning path, compress each maximal consecutive run in one clique to a template visit. This gives a walk visiting each template vertex and using at most w_v visits to v. If the walk starts and ends at the same template vertex, remove its final step and repeated end vertex. Every template vertex is still visited, and the new endpoints are distinct because consecutive visits belonged to distinct cliques. The multigraph of traversed edges is connected and spanning, with odd degrees exactly at its endpoints. Visit counts are the displayed left side. If an edge has multiplicity at least three, delete two copies. Its support remains, every degree keeps its parity, and visit counts only decrease. Iterating leaves multiplicities at most two.

Conversely, a connected multigraph with exactly two odd vertices has an open Euler trail. Its visits to v have exactly the displayed count. Assign one clique vertex to each visit, and distribute any unused vertices of its clique among the visits. Replace each visit by a run of its assigned vertices. All edges between consecutive runs exist by the complete joins, yielding a spanning path in the blow-up.

**Consequences.** The route condition only depends on \(\min(w_v,\deg_H(v))\) for all v: even multigraph degrees are at most \(2\deg_H(v)\) and odd degrees are at most \(2\deg_H(v)-1\). Thus a fixed template has finitely many exact capacity classes, including classes with no upper bound on some module sizes. If S is the set of modules with w_v below \(\deg_H(v)\), then H[w] is traceable whenever H−S is connected and every member of S has a neighbor in H−S. Build a spanning tree of H−S, attaching all S as leaves. Double the spanning tree and reduce the edges along any chosen path from multiplicity two to one. The two ends of that path are the two odd vertices, each leaf visits once, and every other capacity is bounded by its degree in H. In particular a nontraceable blow-up has at least \(\kappa(H)\) modules below their degree capacities, where \(\kappa(H)\) is the vertex connectivity of the template.

## Restriction on support of an infinite family

Suppose the template has minimum degree at least two. In any sequence of qualifying nontraceable blow-ups with unbounded order, pass to a subsequence on which every module is either fixed or tends to infinity, with at least one tending to infinity. Let U be the set of diverging modules. Then **H[U] has at least three components**.

Indeed k tends to infinity. If a diverging vertex is nonuniversal in H, a shortest path to a nonneighbor supplies a vertex at distance two, whose distance cap counts the entire diverging clique. If it is universal, the degree of every vertex grows. Every fixed module with no neighbor in U has bounded degrees, so there can be at most one such module e for large indices, and its size is one. Every other fixed module has an edge to U. All U capacities eventually exceed \(\deg_H(v)\).

If U is connected, take its spanning tree and attach all fixed modules except e as leaves. If e exists, attach it through a neighbor a; the latter is fixed and has already been attached to U. In the resulting spanning tree, double its edges and single the edges along a chosen endpoint path. If e exists choose the endpoint path from e to any vertex in U, so a has one visit as a degree-two interior of this path. Every fixed module now needs exactly one visit and all U capacities suffice.

If U has two components, take spanning trees in them and use a shortest bridge between the two components. It has at most two fixed interior vertices, or exactly three with the middle vertex e: every interior vertex except the first and last cannot see either U component by shortestness, so must be e. Attach each fixed vertex other than e off the bridge as a leaf to one of its neighbors in U. If e exists off the bridge, attach it through an off-bridge fixed neighbor if possible. If no such neighbor exists, e has at least two neighbors and they must be the two bridge interiors a,b, since e has no U neighbor. Replace the bridge edge ab by a-e-b. In either case there is a spanning tree in which the bridge lies along a single endpoint path and all other fixed modules are leaves, except for the one path-interior neighbor of e if e is outside the bridge. Choose the endpoint path between the U trees, starting instead at e if it was attached off the bridge (and ending in the opposite U tree). Doubling the tree and singling the endpoint path again needs only one visit per fixed module. This makes the blow-up traceable for large indices, contradiction.

This restriction applies to arbitrary sequences as well as affine integer weight families. It does not require an asymptotic ratio between order and k.

## Searching a fixed template

For a module v, the positive even-distance count and degree are, respectively,
\[
 E_v(w)=\sum_{d_H(v,u)>0,\ d_H(v,u)\ \mathrm{even}}w_u,
 \qquad D_v(w)=w_v-1+\sum_{uv\in E(H)}w_u.
\]
Distances between different cliques coincide with template distance, and within a clique all distinct vertices are adjacent. As a result, every metric condition is linear on weights once the degree-order case is fixed. The second-smallest degree is exactly k when (i) at most one blown-up vertex has degree below k and (ii) at least two have degree at most k. In the first test an exceptional module must have weight one, and in the second test a single weight-at-least-two module can supply both vertices. The script also imposes the strict order condition \(\sum_v w_v>3k+2\).

The script clique-blowup-routing.py implements a complete bounded-capacity search, subject to the solver returning definite answers and the iteration budget. It queries the exact metric system for a weight assignment. For each satisfying weight vector, it queries the multigraph condition, enforcing connected support via a flow delivering one unit from a fixed root to every other module. If a route with visit vector r exists, it verifies that route independently and excludes all weights that dominate r by adding the linear disjunction that some w_v<r_v. Its route block is sound because a feasible route can absorb unused clique vertices. Any route vector is bounded by the template degrees, so finitely many route cuts can arise. A metric UNSAT after these cuts excludes every nontraceable weight assignment of that base. A routing UNSAT on verified metric weights gives a counterexample.

The replay script verify-clique-blowup.py checks the known qualifying C7 family, and distinguishes the nontraceable unit-weight K1,3 from its traceable center-size-two blow-up. The replay also verifies that the solver rules out all qualifying large-order asymmetric integer weights on four 2-hub templates combining Petersen-minus-edge with split arms, with either hub-edge choice and terminals retained as singletons. In these four examples even the metric system alone was UNSAT, so the result did not rely on routing.

## Collections of blocks demanding endpoints

A block has a connector set A with \(|A|=a\ge2\) and a union of at least a nonempty pairwise anticomplete peripheral cliques. Every peripheral vertex is adjacent to every connector and has no neighbors outside its clique and A. Connector edges are unrestricted, including edges to the rest of the graph.

**Proposition.** If a connected graph contains three pairwise disjoint such blocks, it is nontraceable and violates the Graph 189 metric cap.

For nontraceability, a spanning path having no endpoint in a block's periphery would need at least two path incidences from each peripheral clique to the connectors. This exhausts the at most \(2a\) available connector incidences, leaving no edge on the path from that block to the rest. Thus each block consumes one of the path's two endpoints, impossible.

For the metric cap, at least two of the three blocks have no vertex of degree below k, since only one graph vertex can fail that threshold. In any such block choose x in a smallest peripheral clique of size w. Its degree is \(w-1+a\). It sees every other peripheral clique at distance two, and also every external neighbor of any connector at distance two. If b is the number of these external vertices (at least one by connectivity), it therefore has at least \((a-1)w+b\) distance-two witnesses. The excess over its degree is
\[
 (a-2)(w-1)+(b-1)\ge0.
\]
The metric cap forces equality and in particular b=1 and no additional positive even-distance witnesses. Choose two high blocks. They cannot be adjacent to each other: otherwise each one's unique external neighbor belongs to the other, disconnecting their union from the third block. A peripheral vertex in one has distance at least four from every peripheral vertex in the other. A path with three or fewer edges could only leave through its own connector and arrive through the other connector, requiring an edge between blocks. A shortest path between the two peripheral vertices supplies a distance-four witness, contradicting saturation.

## Heterogeneous two-connector blocks

There is also an exclusion without the complete attachment or internal clique assumptions when every block has two connectors. Let a finite 2-connected graph be partitioned into at least two blocks. Each block has two connector vertices and a periphery with at least two connected components. The only edges between blocks are between connectors. Within a block, contacts and all internal edges are arbitrary.

**Proposition.** Such a graph has no qualifying Graph 189 metric when k≥3. If there are at least three blocks, it also has no spanning path by the preceding endpoint count.

Each connector p touches every peripheral component in its block; otherwise removing the other connector would separate that component. Let A(p) be its number of local peripheral neighbors and let W(p) count local peripheral vertices at distance one or two from p. For any peripheral component where p has a degree-at-least-k contact x, the closed neighborhood of x inside that component has at least k−1 vertices, since x has at most two connector neighbors and no other neighbors outside the component. All these vertices contribute to W(p). Each other peripheral component contributes at least one through its contact. Thus W(p)≥2(k−1) when the block contains no vertex of degree below k, and W(p)≥k always because there is at most one such vertex in the whole graph.

For any inter-block edge pq, the W(p)−A(p) local witnesses of p and the A(q) peripheral contacts of q are all at distance two from p, and are disjoint. Reversing the roles gives
\[
 W(p)-A(p)+A(q)\le k,\qquad W(q)-A(q)+A(p)\le k.
\]
Hence W(p)+W(q)≤2k. But one endpoint lies in a block with no exceptional low-degree vertex, so the sum is at least \(2(k-1)+k>2k\) for k≥3. Connectivity supplies an inter-block edge and gives a contradiction.
