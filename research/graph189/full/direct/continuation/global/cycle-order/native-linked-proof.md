# A linked set in the exterior of the completed longest cycle

Let w be the vertex whose incident edges are completed, let H=G−w, and let P be the longest H-path obtained by opening a longest cycle of that completion. Write k for the second-smallest degree of G, and let d be a lower bound for the original degrees of vertices surviving in H. The argument assumes a nontrivial exterior edge. A high vertex has original degree at least k. At most one vertex is low.

Write λ for the connectivity parameter of the cycle theorem. The actual exterior contains a finite set T of at least λ+1 vertices such that every two distinct members can be joined inside T by a path on at least λ vertices, provided

    λ≥3,   3λ≤k+2,   d≥2λ+2,   2d≥k+6.

The choice w of minimum degree allows d=k. Both λ=s and λ=s+1 meet the conditions at 26≤k, 5≤s, 3s<k. For the arbitrary critical completion use λ=s+1 and d=δ(G). Its existing assumption 2δ(G)≥k+2s+2 implies all four conditions, including at k=3s+1.

## Two exterior-root estimates

For x outside P put qₓ=|N_H(x)−P| and aₓ=|N_H(x)∩P|. At any exterior edge xy, the exact distance-two witnesses on the original longest path give

    aₓ+d_H(y) ≤ k+qₓ,
    aₓ+d_H(y) ≤ k+1+|N_H(x)∩N_H(y)−P|.

For the first bound substitute d_H(x)=qₓ+aₓ. Since d_H(x),d_H(y)≥d−1, one gets qₓ≥2. Consequently every nonisolated exterior vertex x has a high exterior neighbor. If x is high as well, the same inequality at a high-high edge gives 2qₓ≥k−2 and hence qₓ≥λ.

If every nonisolated high exterior vertex has qₓ≥2λ−2, discard the sole possible low vertex. There is still a high-high edge, and each nonisolated retained vertex has internal degree at least 2λ−3. The elementary longest-path degree bound gives an actual exterior cycle on at least 2λ−2 vertices. Rotating it to a prescribed endpoint and choosing the longer of its two arcs gives the required λ-vertex path for each pair on the cycle. Its vertex set has at least λ+1 members.

Otherwise choose a high nonisolated x with qₓ≤2λ−3. The set X consisting of x and all its exterior neighbors has at least λ+1 members and a universal vertex x. For every y in X other than x, its degree in X equals one plus the common exterior neighbor count. The second displayed inequality gives degree in X at least k−qₓ−2 for high y, and at least d−qₓ−2 for all y. Thus every vertex in X has degree at least three and all but at most one have degree at least λ−1.

## Routing in X

In any finite graph with at most one vertex of degree below b, a longest path with a nonisolated prescribed start has at least b+1 vertices. If its last vertex is high, all of that vertex's neighbors lie on the path. Otherwise its penultimate vertex is high. If all neighbors of the penultimate vertex are on the path, the same count applies; if one lies outside, replace the final low vertex by this outside high neighbor and count at the new endpoint of an equally long path.

For distinct prescribed endpoints a,b, reserve the universal vertex and b when neither is universal. In the remaining graph all degrees are positive and all but at most one are at least λ−3. Start at a and use the preceding rooted-path argument, then append the universal vertex followed by b. This gives λ vertices. If one endpoint is universal, reserve it alone and append it at the end, obtaining the same length. The resulting path stays in X. These paths and the long-cycle alternative both satisfy Graph189LinkedExterior.Linked without any assumption about the order of G.

For a minimum deletion the nontraceable original graph and nontraceable deletion already give the exterior edge. For a critical deletion the high minimum-degree gap leaves at least three omitted vertices, whereas an independent exterior can omit at most two. Mapping either witness back into the universal completion acts by the natural inclusion away from w.

This supplies the linked set used by the order-free linked_contra step in @koolkao's proof of the large-order Bondy theorem, upstream blob 1094243524b455ea5dace0862e4c6ec05a7ed312. The disjoint attachments and the final degree count are taken from that upstream proof.
