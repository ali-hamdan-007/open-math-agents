# Exchanges in a minimum spanning cycle-and-edge cover

Let G be a finite simple graph in which each vertex has at most k other vertices at positive even distance and all but at most one vertex have degree at least k. Suppose G has a partition into cyclic pieces, each a cycle of order at least three or a single edge of order two. The previously proved strict expansion supplies such a partition in the high-order two-connected case of Graph 189. Fix one with the fewest pieces and orient each cyclically, interchanging the two vertices on a single edge. The orientation can be reversed on any chosen pieces. All degrees and metric claims refer to G.

Write A(x)=N(x)∖C for a vertex x in piece C, and U(x) for the union of A(q) over the one or two cyclic neighbors q of x. For A outside C write A⁺ and A⁻ for its pointwise cyclic shifts in all the other pieces and H(A)=A⁺∪A⁻. Then the following hold.

1. U(x) is disjoint from H(A(x)). Indeed an edge from q to a cyclic neighbor of a∈A(x), together with xa, joins the spanning path on C from x to q and the spanning path on the other piece from a to that neighbor into a single cycle. This also works for two-vertex pieces, where the path is their edge.
2. Every point of (H(A(x))∪U(x))∖A(x) is at distance exactly two from x. Paths of length two use either an external contact in A(x) or a cyclic neighbor q of x. The resulting exact count of these witnesses is |U(x)|+e(x), where

   e(x)=|H(A(x))|−|A(x)|+|A(x)∖(H(A(x))∪U(x))| ≥ 0.

   Nonnegativity follows because the cyclic successor is a bijection on the exterior. Thus

   |N₂(x)∩C| + |{w:d(x,w) is even and ≥4}| + e(x) + |U(x)| ≤ k.

   If q is a high cyclic neighbor of x, subtracting |A(q)| gives the stronger local consequence

   |N₂(x)∩C| + |{w:d(x,w) is even and ≥4}| + e(x) + |U(x)∖A(q)| + (deg(q)−k) ≤ deg_{G[C]}(q).

3. For consecutive x,q in C, the shifted sets A(x)⁺ and A(q)⁺ have no edge between them. If a∈A(x) and b∈A(q) are in distinct pieces D and E, such an edge a⁺b⁺ joins the three spanning paths on D from a to a⁺, on E from b to b⁺, and on C from q to x into a single cycle. If a and b lie in the same D, they must be distinct for their shifted vertices to be adjacent. By (1), a,b are not consecutive. Thus D has at least four vertices; removing the two edges aa⁺ and bb⁺ gives two path segments, from a⁺ to b and from b⁺ to a, joined by a⁺b⁺ into a spanning b–a path. Closing it through C gives a merged cycle. This proves the assertion including empty sets and pieces of order two. In particular I=(A(x)∩A(q))⁺ is independent, and both x and q have no neighbor in I by (1). Reversing each external piece yields the same result for those chosen orientations.

## Single edges and triangles

For a two-vertex piece xq with q high, (2) gives at most one unit in total for e(x), all vertices at even distance at least four from x, and deg(q)−k. In particular q has degree k or k+1. When G is two-connected, x has eccentricity at most four, since an eccentricity at least five forces at least two vertices in L₄(x) by two-connectivity. If x has a fourth-layer vertex, it is unique, q has degree exactly k, and e(x)=0. Consequently A(x) on each other piece is invariant under advancing two steps around that piece, since |A⁺∪A⁻|=|A| iff A⁺=A⁻. On an odd piece the contact set is empty or all vertices; on an even piece it is empty, one parity class or all vertices. Any external parity-class contact set disjoint from its own shifts must lie in A(q) since e(x)=0.

For a triangle piece xyz with all three vertices high, every ordered pair of distinct vertices q,r in the triangle satisfies |A(r)∖A(q)|+deg(q)−k≤2. Apply (2) at the third vertex. Also |A(q)∪A(r)|≤k by the first inequality in (2), so |A(q)∩A(r)|≥deg(q)+deg(r)−k−4≥k−4. Part (3) consequently supplies an independent set of size at least k−3, all but one of whose vertices are simultaneously at distance exactly two from q and r. Each triangle vertex has ambient degree at most k+2, and its even distances at least four number at most two. More generally for a piece of order m≥2 every high vertex q in it has degree at most k+m−1. This last bound also applies in the presence of low vertices in that same piece.
