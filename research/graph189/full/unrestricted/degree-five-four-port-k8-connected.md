# The connected four-port graph Q at k=8

Keep the notation of degree-five-four-port-overlap.md. Here k=8, each |S_p|≤7 and h≥13. For each p there are at most 3−c_p even-distance witnesses in R, counting its external boundary B_p and the union of S_q−S_p over all ordinary port-neighbors q. The graph Q connects ports that are adjacent or have a common R-neighbor. We assume Q connected and prove impossibility or explicitly produce a spanning path. Ordinary components in this note mean components of G[P].

For an overlapping pair p,q in distinct ordinary components and any x∈S_p∩S_q, put j=|N_P(x)|. The prior intersection bound gives

    |S_p∩S_q| ≥ 3+c_p+c_q−j ≥ 3.

Its proof counts only ports in N_P(x) towards the base inequality c_p+c_q≥j. Thus consecutive overlapping pairs p,q and q,r in three distinct ordinary components force S_p,S_r to intersect: if these were disjoint, r would be an additional distance-two port from q outside the mask of any member of S_p∩S_q. This makes the first intersection at least four. Likewise p is additional in the bound for S_q∩S_r, so that intersection also has at least four members. The two disjoint intersections cannot both fit in S_q of size at most seven.

A failed propagation along an ordinary edge has the following precise form. If a,b are adjacent, c lies in a different ordinary component, S_a∩S_c is nonempty, and S_b∩S_c is empty, then F=S_a∩S_c lies in S_a−S_b. Its at least three vertices are at distance two from b via a. Thus |F|=3, S_a−S_b=F, c_b=0, and F exhausts all even witnesses in R at b.

## Ordinary adjacency connected

A dominating port gives h≤7+3. Otherwise a spanning tree is a four-vertex path. Each of its adjacent central ports has at least one nonneighbor among the remaining ports, since no port dominates, and this nonneighbor is at distance two along the path. Taking the neighborhood of one central port, then its ordinary neighbors' sets and then the other central port's remaining neighbors' sets gives h≤7+2+2=11.

## Three ordinary ports and one singleton

Call the singleton t and write O for its nonempty overlap set in the connected triple. If |O|=3, then c_t=3 and B_t is empty. No core vertex can have t as its sole port, since then its entire degree is at most |S_t|≤7. The core is covered by the triple, whose middle ordinary port sees that union within at most 7+3=10 vertices.

If O is proper, choose an ordinary edge pr leaving O, with p∈O. The failure observation gives |F|=3 for F=S_p∩S_t and saturates r's even budget with F. Since t is an ordinary singleton, c_t≥|O|. For x∈F, every port touching x other than t belongs to O, so j≤|O|+1. Since c_p≥1, equality in the lower bound at F forces c_p=1, c_t=|O| and every member of F to touch all of O.

If |O|=1, p must be adjacent to both other ports of the triple, since any missing port of that connected triple would be at distance two in addition to t. Both other ports thus have their even budgets exhausted by F. A vertex private to t must have a neighbor outside S_t, so it is counted in the boundary of some port of the triple. Neither of the two saturated ports can count this private vertex. Hence all t-private vertices lie in B_p and number at most two. The triple union has order at most 7+2. If |O|=2, the single missing port r has its slots saturated by F, both ports in O have at most two R-even slots, and |B_t|≤1. If any t-private vertices exist, they must all have a neighbor in the same single vertex of B_t. A triple port touching that vertex sees them all at distance two, so there are at most two: r has no free slot for such vertices and each port in O has at most two. Since the triple union has at most 7+3 members, h≤12. This excludes both proper O cases.

## Two ordinary pairs

Call the pairs a,b and c,d. Say a port is active if it overlaps a port of the other pair. All active cross-pairs overlap. Indeed, if a,c overlap but b,c do not, the failed propagation gives c_b=0 and hence b overlaps no opposite port. If there is an inactive port b, its saturation shows that all intersections of the active mate a with opposite active ports are the same three-set F=S_a−S_b. These are all cross intersections. Every member x of F touches all active ports and no others. Let the respective active counts be s,t. For an active cross-pair a,c, x has j=s+t, while c_a≥t and c_c≥s. Its possible neighbors number at most

    j+2+|B_a|+|B_c| ≤ s+t+2+(3−t)+(3−s)=8.

Here the two counts inside F are the other two vertices, and any R-neighbor outside F belongs to B_a∪B_c. Degree eight forces adjacency to both of those other vertices, so F is a clique.

Write W_i for the core vertices contacted by the i-th pair outside F; these two sets are disjoint. On the deficient side W_1=S_b, and since b sees no even core vertices outside S_b other than F, there are no edges between W_1 and W_2. Each |W_i|≤7. For another deficient side this follows by the same saturation argument. For a fully active side the union of its two port neighborhoods has order at most 7+2, since its two ports are adjacent and each sees an opposite port at distance two, and then three F vertices are removed. In each pair a port misses at most two vertices of its W_i. For an active port this uses its ordinary mate and at least one distance-two opposite port; an inactive port misses none. Thus in the block formed by W_i and its two ports, core vertices have degree at least 8−3=5 (only F-neighbors are lost), and each port has degree at least |W_i|−1 including its mate. The marked threshold is |W_i|+3≤10. Every core-core or core-port pair meets it, and the two ports are already adjacent. This gives Hamilton-connectedness of both blocks. End a shell path at an anchor of the first port in a chosen block, span that block to its distinct active port, traverse the clique F, continue through any active port of the other block and span that block. An active port to end the first block at always exists; take its mate as the first port.

It remains to consider both pairs fully active. Every port has c_p≥2. Starting anywhere, the two ordinary edges contribute at most one apiece while any cross overlap contributes at most four, as in the k≥10 paper. Thus h≤7+1+4+1=13 and equality is necessary. The root, the first oriented ordinary edge, and the cross edge in such a spanning tree can each be chosen arbitrarily, so all ports have seven neighbors, all ordinary directional differences have order one, and all cross-intersections have order three (choose the tree to expose the desired cross difference). For a member of any cross-intersection, c_p+c_q≥4 forces its mask size j≥4; hence it touches all four ports. Thus all cross intersections equal a common three-set F. For each ordinary pair the one vertex in its mate's set but not its own occupies the port's only R-even slot. The two mate-only sets in any ordinary pair are distinct singletons. If x∈F had a neighbor y outside F, y would miss both ports of one pair and would be at distance two from both via x, requiring it to be both of their distinct unique witnesses. This is impossible. Now x has at most its four ports and its two peers in F as neighbors, contradicting its required degree.

## One ordinary pair and two ordinary singletons

Write a,b for the pair and c,d for the singletons. If an overlap with c does not propagate along ab, assume S_a∩S_c=F has size three and b is saturated, so b overlaps neither singleton. An overlap between d and a is then necessary: either this holds immediately, or connectedness requires d to overlap c and the strengthened three-component argument at the start forces d to overlap a. Now S_a∩S_d⊆S_a−S_b=F, and the overlap has size at least three. Thus every member of F touches a,c,d, and misses b. But c_a+c_c≥4, since each sees the other and d at distance two. The refined intersection bound gives |F|≥3+4−3=4, a contradiction. Thus all overlaps propagate along ab. The strengthened three-component argument then shows every pair of ports from different ordinary components overlaps.

Now c_c=c_d=3, so B_c=B_d=∅. The nonempty F=S_c∩S_d has no outgoing core edges and has at least five vertices by the degree bound (at most four port neighbors). A member of S_c−S_d would have all its core neighbors in the at-most-two vertices of S_c−F and at most three incident ports, contradicting degree eight. Thus S_c=S_d=F. The ports a,b each have c≥2 and overlap F. The intersection bound gives |S_a∩F|,|S_b∩F|≥3+2+3−4=4. Therefore R−F has at most 2(7−4)=6 vertices, and any of its members would have at most five core and two port neighbors. This contradiction forces R=F, contrary to h≥13.

## Four ordinary singletons

The strengthened three-component observation makes connected Q a clique. All c_p=3, hence all B_p are empty. Adjacent core vertices then have identical masks, since each direction of the adjacency forces mask containment at a vertex outside all boundaries. Every occurring mask class has at least five members by the degree bound. Two such classes cannot share a port since |S_p|≤7. Connected Q and h≥13 are incompatible: each port has a core neighbor (it has at most five neighbors outside R), and more than one disjoint mask class disconnects Q.

This completes all ordinary adjacency patterns. Together with the separate isolated-Q and two-Q-pair proofs, the entire (4,4) case at k=8 is traceable.
