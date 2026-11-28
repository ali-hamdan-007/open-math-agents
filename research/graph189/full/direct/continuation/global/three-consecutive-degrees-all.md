# Traceability for degrees between k and k+2, at every order and degree

**Theorem.** Let G be a finite simple connected graph with second-smallest degree k. Suppose that every vertex has at most k other vertices at positive even graph distance. If every vertex has degree in {k,k+1,k+2}, then G has a Hamiltonian path. The conclusion allows any subset of these degrees, with no connectivity or order restriction.

We write n=|V(G)|, d(x) for the ambient degree, and call a vertex of degree ≥k high. Here every vertex is high. The established small-degree results give the claim for k≤5. The cut-vertex result and all-high separating-pair theorems give the claim at connectivity at most two; see the references at the end. Suppose henceforth that k≥6, κ≥3 and G is nontraceable. The independently audited refined wedge bound gives

    n≤3k+1+(k−2)(Δ−k)≤5k−3.

Choose a longest path P maximizing the sum of squared orders of the connected components of G−P. Choose a smallest component C of G−P, put h=ceil(k/2), and m=|C|. The prior exterior-degree and exterior-size results give d_C(x)≥h for all x∈C and m≥h+2. Every endpoint of any such longest path has all its neighbors on the path.

## Local consequences of the choice of P

For a noncut x of C put q=d_C(x), X=N_C[x], and let R be all vertices of C at ambient distance exactly two from x. Write r=|R|. The P-neighbors of x, called its marks, are neither endpoints nor consecutive. Moreover two of them cannot be two positions apart. Otherwise exchange x for the intervening P vertex y. The middle y has no original C-neighbor: any such contact would allow inserting a path in connected C on the edge from a mark to y, lengthening P. In the equal-length exchanged path, the newly omitted high vertex y needs ≥h omitted neighbors. It therefore joins at least one other original omitted component of order M≥m, while C−x remains connected. The exterior sum of squares increases by at least (m−1)²+(M+1)²−m²−M²>0. This contradicts the choice of P.

Let a_x be the number of marks of x. The predecessors and successors of its marks now give 2a_x distinct distance-two vertices on P. Hence r≤k−2a_x≤2q−k. For each y∈X other than x, the path-contact witness lemma gives at least a_x+a_y distinct vertices of P at distance two from x. Thus a_y+r≤q. Every neighbor of y in C outside X belongs to R. It follows that d_X(y)≥k−a_y−r≥k−q. For x itself, d_X(x)=q≥k−q. Finally every vertex in X has ≤q+r C-neighbors and hence ≥k−q−r≥2k−3q P-neighbors.

We use the following counting conventions. If a disjoint Hamilton-connected subgraph H has p matched contacts to P, the two tails and the p−1 inner gaps between its distinct marks each have ≥|H| unmarked vertices: otherwise the tail or gap is replaceable by a spanning route through H. A bipartite vertex cover smaller than p cannot cover the contact graph if |H|≥p and every H vertex has ≥p contacts, so this latter condition gives the matching by König's theorem. If a disjoint cycle has length L, three disjoint connectors to P exist by Menger: the cycle has at least three vertices and P has at least k+1. Each P-tail has ≥L vertices and each of the two inner gaps ≥ceil(L/2)+1 vertices by the longer cycle arc. In particular |P|≥2L+2ceil(L/2)+5.

## The exterior component is Hamilton-connected

First exclude a cut vertex in C. Choose a smallest leaf block B among the endblocks of C and its articulation w. Put b=|B| and q=min d_B(x) over its noncut vertices. They have d_B(x)=d_C(x)≥h, so B is not a bridge, b≥h+1 and q≥h. Its exterior remainder C−B has size ≥b−1 because it contains the noncut vertices of a second endblock of order at least b.

If b≥2q−1, Fan's circumference theorem gives a cycle in B of length ≥2q−1: every pair at distance two has at least one member of internal degree ≥q. Three connectors and the preceding tail-gap count give n≥b+(b−1)+6q+3≥10q≥5k, a contradiction.

If b≤2q−2 then B−w is Hamilton-connected by minimum internal degree ≥q−1. There are t=max(2,k−b+1) disjoint contact edges from B−w to P. For t=2 a smaller cover together with w would disconnect surviving block interior from P, contrary to κ≥3. The degree lower bound supplies the other possibility, with b−1≥k−b+1 from b≥h+1. Each tail at a matched port can traverse all of B up to w: in B−w traverse to a neighbor of w besides the starting port, possible by 2-connectivity of B. From w continue to a neighbor in C−B and a rooted path of at least h vertices there, since every member of that remainder has lost at most w from its C-neighborhood. The t−1 interior gaps each cost ≥b−1, both tails ≥b+h and |C|≥b+h. Hence

    n≥(t+2)b+3h+1.

For b≥k−1 this exceeds 5k−3 immediately. On h+1≤b≤k−2 the right side is b(k−b+3)+3h+1, concave. At k−2 it is 5k−9+3h>5k−3. At h+1 the excess over 5k−3 is h²−4h+6 for even k and h²−5h+10 for odd k, both positive. This excludes cut vertices.

Now C is two-connected. Choose x of minimum q=d_C(x); it is a noncut vertex. Suppose m≥2q. By Dirac's circumference theorem C contains a cycle of length ≥2q. Its three connectors give n≥m+6q+5≥8q+5. In particular q≤(5k−8)/8≤k−2 and

    a=2k−3q≥(k+24)/8>3.

Apply the local consequences at x. The graph on X has order q+1 and minimum degree ≥k−q, and is Hamilton-connected by 2(k−q)≥q+2. Each of its vertices has at least a marks, and a≤q since q≥k/2. Match a of them. Since r≤2q−k≤q−2, there are vertices in I=C−(X∪R). There are no X–I edges and each member of I has ≥q−r neighbors within I.

Each outer tail can be replaced by a route through all X and at least q−r+2 additional vertices of C. For a prescribed starting X-port v, the graph C−v is connected, so choose a path from X−v to I avoiding v, trimmed to its last X vertex w' and first I vertex y. There is at least one R vertex between them. Traverse X from v to w', follow the trimmed connector to y, and append a path in I starting at y with ≥q−r+1 vertices, by maximality of a rooted path and its end-neighbors. The two tails and a−1 ordinary gaps yield

    5k+1≥n≥m+a+(a+1)(q+1)+2(k−q+2)
               ≥(a+1)q+2a+2k+5.

Substitution q=(2k−a)/3 gives (2a−7)k≤a²−5a−12. But a≥4 and k≥2a imply (2a−7)k≥2a(2a−7)>a²−5a−12, the difference at k=2a being 3(a²−3a+4). This contradiction gives m≤2q−1. The degree-sum Hamilton-connectedness criterion now applies to C itself.

## The only possible contact pattern

There are at least three matched C–P edges: a vertex cover of at most two edges' endpoints would disconnect the surviving vertices in C and P. In particular n≥5m+3, whence m≤k−2. Put a=k−m+1≥3. From m≥h+2 we have k≥2a+2. Each C member needs ≥a P-neighbors. If at least a+1 contacts could be matched on both sides, then n≥(a+3)m+a+1. This exceeds 5k−3 by (a−2)k−a²−a+7≥a²−3a+3>0. Thus the contact matching number is exactly a. A König cover of that size must use only marks: if it used any C vertex, another uncovered C member would have at least a P-neighbors and at most a−1 covered marks. Consequently every C member neighbors the same a marks A, and C is a clique by its ambient degree ≥k. In particular C has no further neighbors anywhere in G outside A.

The marks on every path with the same vertex set as P bound a+1 gaps and tails of ≥m unmarked vertices. Let σ be the sum of their excesses over m. There exists a realization on that vertex set with an endpoint e avoiding adjacency to every mark: the initial endpoint's ≥k neighbors give ≥k distinct rotated endpoints, all different from the opposite fixed endpoint. All these k+1 or more attainable endpoints miss C, and those touching a mark are at distance two from any x∈C, so at most k touch A.

Orient this path from e. In every gap or tail following a mark, e cannot neighbor its first m unmarked vertices, because rotating e at such a vertex would create a new starting endpoint with fewer than m vertices preceding that mark, allowing the tail to grow through C. In the initial tail e can neighbor at most the other vertices of that tail. Since e avoids the marks, this bounds d(e)≤m−1+σ, giving σ≥a. Hence n≥(a+2)m+2a. At a≥4 this exceeds 5k−3 by (a−3)k−a²+a+5≥a²−3a−1>0. Thus a=3, m=k−2, k≥8, n≥5k−4 and |P|≥4k−2.

## Final three-mark contradiction

View our longest path as rooted at its first endpoint. For a fixed exterior x∈C, the rooted-wedge sum applied at its three marks, with their respective successors s, gives

    Σ (d(s)−k) ≤ 3(5k+1−n)/k ≤ 15/k.

Here we used the earlier general wedge sum, d(x)≥k, d(mark)≤k+2 and at most k positive-even witnesses per mark. Since k≥8, at least one such successor w has degree exactly k. No successor touches C, as consecutive C-contact positions would allow inserting a path through connected C. All k−2 members of C are at distance two from w through its preceding mark; thus at most two other vertices outside C are at positive even distance from w.

All remaining vertices outside C apart from w and its neighbors lie at distance three, because every vertex is high and high pairs have distance at most four. Each distance-three target has a penultimate vertex at distance two from w. If that vertex is in C, the target must be a mark, and the mark preceding w is already a neighbor of w. If it is outside C, it is one of the two available even witnesses. At most k targets can lie beyond each such vertex: any of its predecessors in the first layer of w sees all the assigned targets at distance exactly two. This gives |V−C|≤1+k+2+2k+2=3k+5, strictly below |P|≥4k−2 for k≥8. This contradiction completes the theorem.

## Proof dependencies and verification scope

* The prior Graph 189 results used are the complete k≤5 theorem, the cut-vertex and all-high separating-pair theorems (assembled in ../verify/adjacent-degrees.md and ../sep/shallow-high-two-cut.md), the high-pair distance-at-most-four lemma, and the exterior degree and size bounds d_C≥ceil(k/2), |C|≥ceil(k/2)+2 from the previous longest-path checkpoint.
* The matched contact witnesses a_x+a_y are given in ../root/exterior-triangle.md. The maximizing exchange is in optimal-exterior-exchange.md; its necessary one-vertex argument is included above. The root-preserving wedge sum is in ../root/rooted-local-ore.md.
* The sharper order threshold n≤5k−3 used above is the penalty-per-penultimate inequality in ../verify/wedge-order-refinement.md. The independent verification is in refined-wedge-independent-audit.md.
* The classical inputs are König's matching theorem, Menger's theorem, the Hamilton-connectedness degree-sum criterion, Dirac's circumference theorem and Fan's distance-two extension. This is a graph-theoretic paper proof. Prior kernels verify individual degree, contact and rotation steps; no end-to-end Lean theorem is asserted here.
