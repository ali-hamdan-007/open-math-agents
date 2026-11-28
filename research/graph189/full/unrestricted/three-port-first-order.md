# The three-port core of order 2k−2

**Theorem.** In the degree-five disconnected case (a,s)=(3,3), suppose k≥7 and the third layer R has order 2k−2. Then G has a spanning path.

Write P for the three ports and A for the five anchors. Every member of R has a port neighbor, has all its neighbors in R∪P, and has ambient degree at least k. The graph G is 2-connected, so the ports together meet at least two different anchors. As proved in the shell lemma, the shell induced by the anchors, z and K has a Hamilton path between any two prescribed distinct anchors.

## Neighborhood and degree bounds

For every port p put S_p=N(p)∩R. Then |S_p|≤k−1. Indeed take an anchor α incident to p. Every member of S_p is at distance two from α. If α misses some other anchor, that anchor is another even witness through z. Otherwise α is complete to the other anchors. It cannot meet every port because then it would see all 2k−2>k members of R at distance two. A missed port lies at distance two through some other anchor. This gives the claim in both cases.

Every member x of R has at least k−2 neighbors in R. This follows from its ambient degree unless it meets all three ports. In that case every nonneighbor of x in R lies at distance two from x, since it shares a port with x. The at least two anchors incident to the ports are additional distance-two witnesses. Thus
     
    2k−3−d_R(x)+2 ≤ k,     so d_R(x) ≥ k−1.

## Connected core

We use the elementary equality case of the longest-path bound. If H is connected with 2m+2 vertices and minimum degree at least m≥1, then H either has a Hamilton path or is the join of an m-vertex graph and an independent set of size m+2. To see this, suppose H is nontraceable, and take a longest path. The endpoints’ neighbor sets, shifted along the path in opposite roles, are disjoint, since an overlap would close the longest path into a cycle that can be extended by connectedness. Thus the path has at least 2m+1 vertices, hence exactly 2m+1. Denote them v_1,...,v_(2m+1). The single omitted vertex w misses the endpoints and cannot see consecutive path vertices. Its only possible m-element neighborhood is E={v_2,v_4,...,v_(2m)}. Replacing an internal odd-indexed vertex by w gives another longest path. Replacing the first or last vertex by w works as well. In every resulting ordering the even positions are still E, so the omitted odd vertex has precisely E as its neighborhood. This proves the join description.

Apply this with H=G[R] and m=k−2. In the exceptional join let I be the independent set of size k. Every x∈I has exactly k−2 core neighbors and hence at least two port neighbors. All k−1 other members of I lie at distance two. All anchors incident to a port touching x give additional, distinct distance-two witnesses, so those ports share the same singleton anchor neighborhood. Neither three ports nor two different pairs can have this property since collectively the three ports meet at least two anchors. It follows that all members of I are adjacent to the same pair of ports. This violates |S_p|≤k−1. The core therefore has a Hamilton path.

It has a Hamilton path whose endpoints can be assigned distinct ports. To prove this, start with any Hamilton path v_1,...,v_h. If distinct port assignments fail, both endpoints have precisely the same singleton port neighborhood {p}. The endpoint y=v_h then has d_R(y)≥k−1. For each i<h such that yv_i is an edge, the path

    v_1,...,v_i,y,v_(h−1),...,v_(i+1)

has endpoint v_(i+1), taking i=h−1 to mean the original path. These d_R(y) endpoints are distinct and exclude v_1. If none has a port different from p then S_p contains at least 1+d_R(y)≥k distinct vertices, a contradiction.

Write p,t for distinct ports assigned to the endpoints x,y of this path and q for the remaining port. At least one of {q,p} and {q,t} can be assigned distinct anchors. Failure for both would force all three ports to have the same sole anchor. Orient so that {q,p} has distinct assigned anchors. The path q, shell, p, x, core path, y, t spans G.

## Disconnected core

Each core component has size at least k−1 by the core minimum-degree bound. The core therefore consists of exactly two (k−1)-cliques C_1,C_2. For each clique at least two different ports and at least two different vertices of the clique occur among its port contacts, by 2-connectivity of G. Its incidence graph with P thus has a matching of size two. Call a port pair usable when such a matching covers its two ports.

If distinct pairs can be chosen for the two cliques, name them {p,q} and {q,t}. Using their matched contacts and the clique paths gives p,C_1,q,C_2,t. Append the shell at the initial port.

Otherwise both cliques have the same unique usable pair {p,q}. The third port t has no contact in either clique. Indeed any t-contact x together with a p- or q-contact different from x would give a different usable pair, and the matching for p,q has distinct contacts. Since D=R∪P is connected, t is adjacent to p or q; name a neighbor p. Use t,p,C_1,q,C_2, taking a path through the last clique from any q-contact. Append the shell at t.

All routes use only original edges. This proves the theorem for every k≥7, simultaneously for all split parameters and also when the universal set is empty.
