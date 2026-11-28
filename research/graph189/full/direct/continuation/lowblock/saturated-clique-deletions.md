# Saturated cliques in a minimum counterexample

Let G be a minimum-order counterexample to Graph 189. Write δ,k for its two smallest degrees, n for its order, h=ceil(k/2), and q=ceil((n−3k−1)/k). Let b(v)=δ when v neighbors the unique low vertex of degree δ<k, and b(v)=k otherwise. A saturated vertex has k other vertices at positive even distance. At least one of the following occurs:

1. Some saturated v has d(v)≥b(v)+q.
2. There are 2≤j≤q+1 mutually adjacent saturated vertices and a common neighbor x outside them of degree at most k+j−2.

Thus in the second outcome a pair of saturated vertices must have a common neighbor of degree at most k if j=2; for j=3 the four-clique must have its additional member of degree at most k+1. Under failure of the first outcome it suffices to prove existence of the second for any j≥2: if j≥q+2, one member of that saturated clique has degree at most k+q−1 and can serve as x for q+1 of the others.

Assume neither outcome. The established reductions give n≥3k+3, k≥6, n≤1+δ+k+floor((k+1)²/4), and every longest path misses at least h+2 vertices. Write e(v) for the positive even count. We use the local wedge bound: in any graph with cap k and order n', for nonadjacent neighbors a,b of v having v as their only common neighbor,

    n'≤3k+1+k(d(v)+e(v)−d(a)−d(b)).

This follows from the independently proved wedge-order paper since its local defect j is positive in this case.

## Separated maximal cliques of saturated vertices

From a pool initially containing every saturated vertex, take any inclusion-maximal clique K of that pool, select every member, and discard from the pool all vertices at distance at most two from K. Repeat until the pool is empty. An unselected saturated vertex discarded at a step has positive even distance from some member of K. Otherwise its distances from members of K are all odd. They differ by at most one and their minimum is at most two, so all would be one, contrary to maximality within the current pool. The selected cliques are mutually at distance at least three. Let S be their union and r their number. The pool is nonempty initially: in the absence of saturation one can isometrically delete a minimum vertex and its surviving cap would be at most k−1, as proved in minimal-counterexample-minors.md.

For every selected clique K of size c≥3, each member x is high and satisfies d(x)≥k+c−2, because x is adjacent to the other c−1≥2 mutually adjacent saturated members. A member below that bound would give the second outcome. All such x also satisfy d(x)≤k+q−1, so c≤q+1 and q≥2. A clique containing the unique low vertex therefore has size at most two. For c=2 the same lower bound d(x)≥k+c−2 holds for each high member by definition.

Deleting each selected clique is isometric. Order its members by nondecreasing original degree; suppose i earlier members of the clique have been isometrically deleted, and v is the next one. Its degree is d(v)−i and e(v) has not changed because the deleted vertices were adjacent to it. While v remains, each exterior high neighbor y of v has current degree at least k. Indeed if y originally had j≥2 neighbors in K, then d(y)≥k+j−1 by exclusion of the second outcome, and at most j−1 of them have gone. If j=1 then none have gone. An exterior low neighbor of v keeps its original degree: it cannot have two neighbors in K without the second outcome.

For nonadjacent current neighbors a,b of v, at most one lies in K. If both are exterior, their degree sum is at least b(v)+k, giving local excess at most q−1−i. Since n−3k−1>k(q−1), we have n−i>3k+1+k(q−1−i). Therefore they possess an alternate common neighbor, by the local wedge bound.

If a is in K and b exterior, the deletion order gives d_current(a)≥d(v)−i. The local excess is thus at most k−d_current(b). For i=0 the original wedge is already safe: both neighbor degrees sum to at least b(v)+k, giving excess at most q−1. For i≥1 there is at least one other clique member still present, so c≥3, q≥2, and i≤c−2≤q−1. If b is high the excess is at most zero, whereas n−i>3k+1. If b is low then v neighbors that unique low vertex, and k+c−2≤d(v)≤δ+q−1 gives k−δ≤q−c+1≤q−1−i. The same strict order bound as above again forces an alternate common neighbor.

All nonadjacent pairs of v-neighbors thus have a two-edge detour avoiding v, which permits replacing every geodesic segment through it. This proves sequential isometry inside the clique. Every local detour just used lies within distance two of v in G, hence survives deletions inside every other selected clique. Deleting all of S preserves survivor distances. A surviving high vertex with neighbors in a selected clique has no neighbors in another selected clique. Losing j neighbors preserves degree at least k−1 for j≤1, and for j≥2 its original degree was at least k+j−1 by exclusion of the second outcome. Thus at most one survivor has degree below k−1. Because of the even coverage of all surviving saturated vertices, G−S satisfies the Graph 189 hypothesis and has a spanning path P by minimum order. At least three vertices survive: in a selected clique of size c≥2 a high member has at least k−1 neighbors outside it, none in another selected block. A singleton has at least δ≥3 such neighbors.

## Recovering all but one vertex per block

Disjoint closed neighborhoods of one vertex per selected block imply

    δ+1+(r−1)(k+1)≤n,    r< (k+1)/4+2.

In particular r≤h, and r<k/2 except possibly k=6,r=3 or k=8,r=4. In either exceptional case at least one selected block has size at most two. For k=6 the order bound gives n≤25 and q≤1, ruling out any clique of size three by the earlier degree estimates. For k=8 and four blocks of size at least three, a representative of each would have degree at least k+1. Their disjoint closed neighborhoods give n≥4(k+2)=40, contrary to n≤37.

Process the all-high blocks one at a time. Leave a block containing the low vertex entirely to the end. In the exceptional cases r=k/2 leave some block of size at most two to the end instead if there is no low block; a low block already has size at most two. In each processed block we construct a new path with at most one additional omission from previously included vertices and the current block together. Thus at most one vertex per completed block remains unaccounted for, and every unprocessed block has all its vertices outside the current path.

A singleton may simply be left out. For an all-high block of original size c≥2, let T consist of its members not yet inserted. If one member has an edge to a path endpoint or edges to consecutive path vertices, insert that member without dropping a path vertex, and repeat. Stop successfully if |T|≤1. Otherwise write A_x for the current path contacts of x∈T. At this step let p be the number of earlier processed blocks. No original member of a different selected block is adjacent to x. Besides internal block vertices outside the current path, each earlier processed block accounts for at most one omitted vertex from those originally on P or already processed. Thus

    |A_x|≥d(x)−(c−1)−p≥k−1−p.

Here d(x)≥k+c−2 for c≥3 and d(x)≥k for c=2. For ordinary cases p≤r−1 and r<k/2, so 2|A_x|>k. In the exceptional cases only the first r−1 blocks are being processed and p≤r−2, giving the same strict inequality.

Suppose there are no contacts one or two positions apart from distinct members of T. For a fixed x, after the direct insertions stopped, A_x avoids endpoints and consecutive positions. Its shifts on the path then comprise |A_x|+s_x distance-two vertices, where s_x is the number of its maximal runs at step two. For another y∈T, A_y∖A_x supplies additional distance-two vertices via xy, disjoint from the shifts by absence of one-position cross contacts. Each common contact in A_x∩A_y belongs to a singleton run of A_x, by absence of two-position cross contacts. Hence

    k≥ |A_x|+s_x+|A_y∖A_x|≥ |A_x|+|A_y|>k.

There are therefore contacts one or two positions apart from distinct x,y∈T. Replace the intervening path portion, with zero or one interior vertex, by a spanning x-to-y path in the clique T. This inserts all of T and drops at most one old path vertex, as claimed.

When r<k/2 and there is no low block, the final path misses at most r vertices. When the low block or exceptional last block was skipped, it misses at most (r−1)+2≤h+1. This violates the universal gap in longest path orders and proves the theorem.
