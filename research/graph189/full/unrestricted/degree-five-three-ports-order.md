# A uniform order bound for the three-port shell

Let z be the unique degree-five vertex of a qualifying graph, let all other vertices have degree at least k≥7, and retain the disconnected (a,s)=(3,3) shell. Thus |K|=k−3, the three ports P meet the third layer R in sets S_p covering R, and every neighbor of a vertex of R lies in P∪R. Put h=|R|. If h>k, then

    h ≤ floor((3k+3)/2).

In particular h≥2k−1 is impossible. Here a positive even-distance count of at most k holds at every vertex.

1. No anchor meets all three ports. Otherwise the whole of R is at distance exactly two from this anchor. Also |S_p|≤k−1 for each p. To see this fix an anchor α adjacent to p. Each member of S_p is at distance two from α. If α misses another anchor, that anchor is at distance two through z. If α sees all other anchors, choose a port q that α misses; α sees some anchor of q, so q is at distance two from α. In both cases one more witness lies outside R.

2. For each p set B_p=N_R(S_p)−S_p, the external vertex boundary in R. Then |B_p|≤2, since B_p is wholly at distance two from p, and p has at least k−2 distance-two witnesses outside R. For p with at least two anchors, every member of K sees at least four of the five anchors (its remaining potential neighbors are the other k−4 vertices of K). Thus K∪{z} supplies k−2 witnesses. For a sole-anchor port p with anchor α, any common neighbor of p and α would have to be another port adjacent to α. There is at most one such port by paragraph 1. Hence at least deg(α)−1−1≥k−2 neighbors of α are different from p and nonadjacent to p. All lie outside R. This yields the claimed boundary estimate for every p.

3. Let X be the vertices of R with a unique port neighbor. If x∈X touches p, its possible neighbors in S_p∪P number at most |S_p|, including p. This is at most k−1, so x has a neighbor y in R−S_p. Choose q with y∈S_q. Then q≠p and x∉S_q, whence x∈B_q. Consequently |X|≤∑_q |B_q|≤6.

4. Summing the three incidence-set sizes now gives 2h−|X|≤∑_p|S_p|≤3(k−1). Rearrangement gives the bound. Since 2(2k−1)−3(k−1)=k+1>6, this excludes all the higher orders.

Together with the previously established h=2k−3 and h=2k−2 spanning routes and the small-order theorem, this disposes of the full disconnected (3,3) parameter pair. Only the order bound above is new here.
