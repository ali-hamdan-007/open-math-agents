# Two covering anchors give an order bound at a degree-three vertex

Let G be finite, z a vertex of degree three, A=N(z), and Lᵢ its distance-i layer, with T=L₂. Suppose every vertex has at most k other vertices at positive even distance, all other vertices have degree at least k, and any two other vertices are at distance at most four. The high-pair distance bound gives eccentricity at most five at z. For y∈L₅ and every a∈A, triangle inequality gives d(a,y)≥4, hence equality. Put d=k−|T|; the even-distance bound at z gives |L₄|≤d.

Suppose two anchors a,b cover T, meaning T⊆N(a)∪N(b). Every vertex of L₃ has a neighbor in T, so it is at distance exactly two from at least one of a,b. Every vertex of L₅ is at distance four from both. If a single anchor covers T, that anchor already gives |L₃|+|L₅|≤k. Therefore n≤4+|T|+k+d=2k+4.

Otherwise both a and b miss vertices in T. If they are adjacent, every T vertex missed by a sees b and has distance two from a; the reverse statement holds for b. If a,b are nonadjacent, they have distance two from each other via z. Thus each anchor has at least one even-distance witness outside L₃∪L₅. Summing yields |L₃|+2|L₅|≤2k−2, giving

    n = 4+|T|+|L₃|+|L₄|+|L₅| ≤ 3k+2.

Consequently at n>3k+2 every anchor i has a private port, a member of T whose only neighbor in A is i: apply failure of covering for the other two anchors. These three distinct private ports imply that i misses at least two T vertices. Write aᵢ=|N(i)∩A|. Since all neighbors of i are in {z}∪A∪T, the number of T vertices missed by i is at most 1+aᵢ−d. After the two compulsory misses it has at most aᵢ−1−d further misses. Thus the three anchors induce a path or a triangle, d≤1, and d=1 requires a triangle. This also ensures that the one-ended splice in the two-component routing lemma always has its required anchor edge in this order range.

Number the anchors with bits 1,2,4 and represent a port by its nonempty anchor-neighborhood mask. All unlisted masks below are 7; list all masks different from 7 with multiplicity, up to permuting anchors (for the path, bit 1 is its center). With a path d=0 and the list is (1,2,4) or (1,2,4,6), according as the remaining center miss is unused or used. For a triangle and d=1 the list is (1,2,4). For a triangle and d=0 the list is one of

    (1,2,4),  (1,1,2,4),  (1,2,3,4),  (1,1,2,4,6),
    (1,2,3,4,5),  (1,2,3,4,5,6).

Indeed each anchor has a single remaining miss. Each extra double mask uses one seat and each extra private uses two; the sets of used seats must be pairwise disjoint. These are precisely the resulting possibilities. This extends the rooted templates in the prior degree-three residual analysis to arbitrary eccentricity.

In particular, eccentricity at least four forces d=1, |L₄|=1 and the triangle with exactly one private per anchor. A fifth layer is impossible in a 2-connected G, since the unique L₄ vertex would separate it from z. Thus every order-above-3k+2 residual is either of eccentricity three or of eccentricity four with this singleton fourth layer.
