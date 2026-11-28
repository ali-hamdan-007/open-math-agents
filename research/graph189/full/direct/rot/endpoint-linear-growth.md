# A linear lower bound on the attainable high endpoints

Under the full Graph 189 assumptions and 2-connectivity, let P be a longest nonspanning path. Take the family of paths obtained by Pósa rotations at either endpoint, identifying reversal of an undirected path. Let R be the set of endpoints in this family and t=|R|−k−1. Then k≤2t. In particular at least k+ceil(k/2) high endpoints are attainable, and every omitted vertex sees at least ceil(k/2) high attainable endpoints at odd distance ≥3. If the omitted vertex is high, all these odd distances are three by the registered diameter and distance-five results. The result for unrestricted paths on the same vertex set follows by containment; the rotation class is used to establish the block invariants.

Every endpoint in R has at least k compatible mates, as proved in `remote-endpoint.md`; compatible pairs are nonadjacent. Consequently d_R(r)≤t for every r∈R. Put q=max d_R(r). The same file establishes t≥1. If k≤t+1 the conclusion k≤2t already follows. Hence assume k≥t+2. For a high r, the predecessors of its pivot neighbors include at least k−1−d_R(r) distance-two vertices of R (discard r itself and its R-neighbors). At most t−d_R(r) nonneighbors in R are incompatible with r, since all d_R(r) neighbors are incompatible. Thus some distance-two vertex f is compatible with r. Starting again on a path from r to f, this f adds one distance-two witness outside the pivot predecessors, giving

    1≤|F_r|≤k−d(r)+d_R(r)≤d_R(r),

where F_r denotes the other vertices at even distance from r outside R. Here nonemptiness follows from the last or penultimate vertex of a geodesic to any omitted vertex, as in `endpoint-matching.md`.

There are two compatible high endpoints u,v at odd distance. Otherwise, for every high r all its compatible high mates are at positive even distance (compatible distinct mates are nonadjacent). There are at least k compatible mates and |F_r|≥1, so R would contain a unique low vertex z, compatible with every high r. Exactly k−1 compatible high mates exhaust all the available even-distance places in R for each high r, forcing z to be at odd distance from r. Moreover z is nonadjacent to each r by compatibility. Orient a path from z. All its neighbors lie on the path, and each of their predecessors lies in R by rotation. Every predecessor other than z would be high and would share a neighbor with z, forcing distance two, impossible. Thus the immediate successor is the only neighbor of z, contrary to 2-connectivity.

The edges of the path between vertices outside R are invariant as an unordered set under rotations: a pivot deletes one edge incident with a new endpoint in R and adds one incident with the old endpoint in R. Thus the maximal nonempty blocks of vertices outside R are invariant as unoriented paths, including singleton blocks. Also the number h of R-R path edges is invariant, since the deleted and added edges share the same pivot, with both exchanged endpoints in R. Let m be the number of nonsingleton blocks and J the set of singleton blocks, identified with their vertices, with j=|J|. Each gap between consecutive R positions either has no interior vertices, is a singleton, or is a nonsingleton block. Therefore j=k+t−h−m.

Orient a path in the family from this compatible odd pair u to v and put q_u=d_R(u), q_v=d_R(v). From u, each R-neighbor pivot produces an R-R path edge with the pivot as its right endpoint. From v, each R-neighbor pivot gives an R-R path edge with the pivot as its left endpoint. These two families are disjoint. An edge whose left endpoint is adjacent to v and whose right endpoint is adjacent to u would close a cycle on V(P): travel from u to its left endpoint, use the chord to v, traverse P backward to its right endpoint and close to u. Such a cycle can be opened and extended into an omitted vertex, contradicting maximality. Hence h≥q_u+q_v.

From either r=u or r=v every neighbor pivot outside R is the entry of its own block in the orientation from r, since its predecessor is attainable. If the block is nonsingleton, its second vertex cannot be adjacent to r: pivoting through it would expose its predecessor outside R. Thus it is a member of F_r, at distance two from r. Different blocks give distinct witnesses. At most min(q_r,m) of r's neighbors are in nonsingleton blocks, so r has at least k−q_r−min(q_r,m) neighbors in J. The distance of u from v is odd and at least three, so their neighborhoods are disjoint. Summing their two bounds within the j-element set J gives

    k ≤ t−h−m+q_u+q_v+min(q_u,m)+min(q_v,m)
      ≤ t+min(q_u,q_v) ≤ 2t.

For the second inequality use h≥q_u+q_v and min(q_u,m)+min(q_v,m)−m≤min(q_u,q_v). This proves the result.

For k≥t+2 the same proof gives a simultaneous statement about the high compatible odd pair u,v. For r=u,v let b_r count the omitted vertices at positive even distance from r. These consume b_r places of F_r separate from all the second block vertices on P. Thus each r has at most min(q_r−b_r,m) neighbors in nonsingleton blocks, and the same sum yields

    k ≤ t+min(q_u−b_u,q_v−b_v).

In particular b_u,b_v≤2t−k. All but at most 4t−2k omitted vertices have odd distance from both ends of this path. If k=2t, every omitted vertex has odd distance from both endpoints at once. The statement applies to every compatible high odd pair; existence of such a pair used only the original even cap and the nonempty external witnesses F_r.
