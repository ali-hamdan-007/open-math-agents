# The second layer misses at most three slots at a high-order degree-five root

Let z be the unique degree-five vertex, let every other vertex have degree at least k≥7, and let the positive even-distance cap be k. In the diameter-at-most-four regime, assume n>3k+2. Write A=N(z), T=L₂(z), R=L₃(z), F=L₄(z), d=k−|T|, s=|F|. If d≥4, then G has a Hamilton path. This applies in particular to the remaining connected closed-neighborhood-complement case.

An anchor has only z, the other four anchors and T as possible neighbors, so d≤5. The cap at z implies s≤d and the order gives

    h=|R|≥2k−3+d−s.

If an anchor covers T, all R are at distance two from it, contrary to h>k. Thus each anchor misses at least one member of T. Since it misses at most 5−d by its degree, d=5 is impossible. At d=4 every anchor misses exactly one member of T and is adjacent to all four other anchors. Its missed member of T is at distance two through an anchor. Consequently each anchor sees at most k−1 vertices of R at distance two.

## Forced layers when d=4

Two anchors with different missed vertices cover T, so together they see all of R in two steps. Their common visible set in R has at most 2k−2−h≤1 member. There must be at least two distinct misses, since every T vertex has an anchor. If there were at least three, then for any t∈T one could choose a pair of anchors missing two different vertices other than t. The vertex t touches both, so has at most one neighbor in R. This would give h≤|T|. Thus exactly two T vertices x,y occur as misses. Let A_x and A_y respectively consist of the anchors touching x and y; these partition A into nonempty sets. All W=T−{x,y} are complete to A, and |W|=k−6≥1.

Pick anchors of the two types. Every R-neighbor of W is visible to both, so the union of all such neighborhoods has at most one member. If a vertex w∈W had no R-neighbor, it would need all five anchors and all |T|−1 other members of T to attain k. It would touch x,y, and see all h vertices of R in two steps, impossible. Thus every w has the same unique R-neighbor v. We get equality h=2k−3, s=4, and v is the sole common-visible member. The two exclusive sets X,Y have |X|=|Y|=k−2 and satisfy X⊆N(x), Y⊆N(y). Their members have exactly the indicated port in T.

Every w misses at most one peer in T by its degree. It cannot touch both x,y, as all R−{v} would then be at distance two from it. Thus it touches exactly one, is complete to the other W, and meets v. If w touches x, the vertices z,y and all k−2 members of X spend its entire even budget. Consequently v has no neighbor in F or Y (each such vertex would be another distance-two witness at w). A w touching y gives the symmetric exclusion. Both w-types cannot occur, since v would then have possible neighbors only in W∪{x,y}, of size k−4. Relabel so every w touches x.

Every anchor's k−1 visible R-vertices and missed T-vertex spend its full even budget. It is at distance three from every f∈F, since distance two is excluded by layers and distance four exceeds its even budget. Each shortest anchor-to-f path uses T followed by R. Because the only neighbor in R of W is v and v misses F, every f therefore meets both X and Y.

At y, the k−6 vertices of W, z, all members of A_x, and all four vertices of F are distinct distance-two witnesses. It follows that |A_x|=1 and these use its entire even budget. Thus X,Y have no cross edge. Nor are x,y adjacent, because such an edge would put X at distance two from y. Finally y is not adjacent to v: the high degree of v forces at least four neighbors in X (its other possible neighbors are W and x,y), any one of which would then be at distance two from y.

## Assigning four fourth-layer vertices

Each f has all its neighbors in X∪Y∪F. Partition F into F_X,F_Y, maximizing the sum over f of its number of neighbors in its assigned core side, minus the number of nonadjacent pairs of F in the same part. For any fixed f its scores for the two potential placements are

    d_C(f)−2−number of nonneighbors of f among F−{f} assigned to C,

where C=X or Y. Their sum is d_G(f)−7≥0. Moving f changes the objective by its score gain, so at a maximum f has nonnegative score in its assigned side. With t=|F_C| this says

    d_C(f)+d_(F_C)(f)≥t+1.

We can also ensure F_X is nonempty. Each member of X needs an F-neighbor, as its other possible neighbors are X−{itself}, x and v, at most k−1 in number. Since |X|=k−2≥5, some f has at least two X-neighbors. If F_X is empty, move this f to X. It meets its new bound t+1=2; for every other f the threshold falls by one and the internal degree by at most one.

## Port-rooted paths through the two sides

For k≥8 use cores C=X and C=Y. Join each to all its assigned F_C and its own port p=x or y, and adjoin a new leaf at p. The augmented order is k+t and the Hamilton-path closure threshold is k+t−1. For C=X each core vertex retains degree at least k−5+t (only v and the 4−t unassigned members of F can be lost); for C=Y its degree is at least k−4+t. Thus every missing core pair in X meets the threshold because k+t≥9, using F_X nonempty. For Y it suffices that k+t≥7. Selective path closure makes C a clique.

When k=7 there is one member of W. Use C=X∪{v} on the x-side. The previous exclusions leave v just five X-vertices, x and the one W-vertex as possible neighbors, so it is adjacent to all seven. This six-vertex core is complete to x. The augmented order is 8+t and threshold 7+t. Each original X vertex retains at least 3+t neighbors, and v retains six. Since t≥1 every missing pair of X-vertices closes; v already meets all of X. The ordinary Y-side computation above still applies.

In every closed side, a core vertex now has degree at least |C| from its peers and p. Each assigned fourth-layer vertex has degree at least t+1 from its original side contacts and assigned F-neighbors. Every missing pair between it and C thus meets the threshold |C|+t+1 and closes. As |C|≥t+1, order the clique to place the t fourth-layer vertices between distinct consecutive core vertices, starting with the leaf and p. Reverse closure and remove the leaf. This gives a spanning path of each original side rooted at its port.

To join these paths, use the shell between x and y. At k≥8, begin x,w₁,v,w₂, followed by all other W. At k=7 begin x,w₁; there v was included in the x-side path. From the last W vertex traverse the five anchors, with z inserted between two of them, ending at an anchor of y, and finish at y. All W touch all anchors and the anchors form a clique. Concatenating the original port-rooted paths at x,y through this shell gives a Hamilton path of G.
