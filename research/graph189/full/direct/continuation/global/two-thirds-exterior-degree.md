# A two-thirds internal degree bound on an optimized exterior endblock

Choose a longest path P maximizing the sum of squared exterior component sizes. Let C be its smallest high-bearing exterior component, and let x be a high vertex of C that is not a cut vertex of C. Write q=deg_C(x). The following implication holds for k≥3:

    3q≤2k−3   ⇒   (q+1)(2k−3q+1)≤n+1.

It follows uniformly that

    q > (2k−2√(3k)−5)/3.

In fact the proof applies to every high x in any sole high-bearing exterior component of an arbitrary longest path, including cut vertices, because the one-vertex exchange there needs no optimization or noncut assumption.

Write a_x for the number of neighbors of x on P, X=N_C[x], and r for the number of vertices of C at ambient distance exactly two from x. The square-maximizing exchange in optimal-exterior-exchange.md proves that successive neighbors of x on P cannot occur two positions apart, with the only exception of two marks either side of the unique low path vertex. Their predecessor and successor positions therefore give at least 2a_x−1 distinct distance-two vertices on P. This implies

    r≤k−2a_x+1≤2q−k+1.

For any high neighbor y of x in C, the checked path witness lemma in ../root/exterior-triangle.md gives at least a_x+a_y distinct distance-two vertices on P from x. Hence a_y+r≤k−a_x≤q. Every C-neighbor of y outside X belongs to the r-count. Thus y's degree inside X is at least k−a_y−r≥k−q. The same bound holds for x because q≥ceil(k/2).

Delete the possible low member of X and call the remaining induced graph H. Its order is q+1−e, where e is zero or one, and minimum degree at least k−q−e. If 3q≤2k−3, then twice this minimum degree is at least |H|+1. Hence H is Hamilton-connected. In addition every member y of H has at most q+r neighbors inside C: when y≠x they belong to the q other vertices of X or the r second-layer vertices, and the bound is immediate for y=x. Therefore each has at least a=k−q−r≥2k−3q−1 contacts on P. Use a₀=2k−3q−1≤q, since q≥ceil(k/2). Any vertex cover of the H–P edges of size less than a₀ would leave an uncovered H vertex with a missing contact. Thus there is a matching of size a₀. Its two tails and each intermediate gap have at least |H| unmarked vertices by Hamilton-connected routing through the disjoint H and longestness of P. We conclude

    n≥|C|+a₀+(a₀+1)|H|≥(q+1)(a₀+2)−1.

The prior n≤1+3k+√(3k³) and q+1≥k/2+1 imply (n+1)/(q+1)<6+2√(3k). In the other case 3q>2k−3 the stated simpler lower bound holds immediately.

An optimized C therefore contains a two-connected good block B on b vertices for which all but at most one vertex have degree inside B exceeding the displayed lower bound: take C itself when it is two-connected (its possible low vertex is the exception), otherwise take an endblock whose noncut vertices are all high, exempting its unique articulation. A leaf bridge cannot have such a noncut high vertex by the original ceil(k/2) interior bound. Fan's theorem gives a disjoint cycle of length at least min(b, 2d), where d is the least integer strictly greater than (2k−2√(3k)−5)/3.

A complementary conclusion holds when b≤2d−2. Remove the exceptional vertex, or any vertex if C was wholly high and two-connected. The b−1 remaining vertices have minimum internal degree at least d−1, hence induce a Hamilton-connected graph J. Any t pairwise disjoint J–P contact edges supply the two tails and t−1 gaps through J, yielding

    n ≥ b+t+(t+1)(b−1) = (t+2)b−1.

The maximum matching size t is thus at most floor((n+1)/b)−2. By König there are sets Y⊆J, A⊆P with |Y|+|A|≤t covering every contact edge. Every vertex of J−Y has all its P-neighbors in A, all its C-neighbors inside B, and degree at least k. It has ≥k−|A|−|Y|−1≥k−t−1 neighbors in J−Y. Its entire external neighborhood lies in A∪Y together with the one deleted block vertex. Thus either G has a cycle disjoint from P of length at least 2d−1, or it has such a high-degree induced subgraph on ≥b−t−1 vertices with boundary at most t+1. The previous b>k−√(3k)−6 bound makes t=O(√k).

## Consequence for vertex connectivity

For k≥600 write u=√(3k), so n≤k(u+3)+1. Then

    κ(G) ≤ (3/2)√(3k)+6.

In the small-block case the boundary of W separates its nonempty high core from P−A. By b>k−u−6 in near-degree-exterior.md, its order is at most (n+1)/b−1≤u+7. Here (u+8)(k−u−6)−(k(u+3)+2)=2k−14u−50>0 at k≥600; the bound also ensures b>t+1 and |P|>|A|. In the other case the disjoint cycle has length L≥2d−1>(4k−4u−13)/3. The earlier κ≤2u+15 ensures κ≤L, and |P|≥L. The κ disjoint Menger connectors give n≥3L+κ+(κ−1)(ceil(L/2)+1)≥(κ+5)L/2. Thus κ≤2n/L−5≤3u/2+6. For the last arithmetic, (3u/2+11)(4k−4u−13)−6(k(u+3)+1)=8k−(127/2)u−149, positive at k=600 and increasing thereafter.
