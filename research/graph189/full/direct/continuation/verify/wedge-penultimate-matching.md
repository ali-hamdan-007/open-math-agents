# A matching bound on a local Ore obstruction

Let G satisfy Graph 189 and use k,e,j and the induced path u,w,v from wedge-order-refinement.md. Set K=1+d(w)+e(w)−d(u)−d(v)−j. There exist integers t≥0 and ε∈{0,1} with t+ε≤K such that

    n≤3k+2−j+t(k−t−1)+ε.

Suppose the local excess d(w)+e(w)−d(u)−d(v) is at most r on the induced wedges whose endpoints differ from z, where 0≤r≤floor((k−1)/2). A Hamilton path starts at z whenever

    n>3k+1+r(k−r−1).

Thus if z has minimum degree we may take r=Δ−k. At r≥2 this cutoff saves r(r−1) beyond the previous linear estimate. The matching result is a paper proof.

Let T consist of vertices at a common odd distance ≥3 from u,w,v. Let ε count those at distance ≥5. By the high-pair distance bound ε≤1, since any such vertex is low. The remaining T₃ vertices are at common distance three. Assign each to a penultimate vertex on a shortest path from w. Each active penultimate a lies at distance two from w and has no edge to either wedge endpoint. Form the bipartite graph between these active penultimates and their first-layer predecessors. Choose any maximal matching of size t, with pairs (b_i,a_i), b_i adjacent to w. Each unmatched active penultimate has a matched predecessor, by maximality. Assign it to some such predecessor, assign each matched penultimate to its partner, and group all T₃ targets by these predecessors. Every matched penultimate serves at least one original target; designate one target x_i assigned to a_i.

For a matched predecessor b_i put c_i=|{u,v}∩N(b_i)|. Because its partner a_i misses both endpoints, b_i is neither endpoint. The even budget at b_i includes all the targets grouped with it: they have a two-edge walk from b_i and are two w-layers beyond b_i. Its budget also includes each of the 2−c_i wedge endpoints not adjacent to it, via w. Finally every j≠i provides a further, distinct distance-two vertex. Use x_j if b_i is adjacent to a_j. Otherwise use a_j if b_i is adjacent to b_j, and b_j via w in the remaining case. These witnesses lie in three distinct w-layers according to type, are distinct within each layer, and a target from another group is disjoint from the i group. None coincides with an endpoint since all matched predecessors avoid the endpoints. Consequently |T₃|≤t(k−t−1)+Σc_i, with the empty matching allowed when T₃ is empty.

Each matched penultimate occurs in the closed even set of w and in the even set of any endpoint adjacent to its predecessor, giving c_i duplicate incidences beyond those in Q=N(w) outside N(u)∪N(v). The earlier closed-even cover therefore gives |T|≥n−3k−2+j+Σc_i. At most K candidates are available (the size formula in wedge-order-refinement.md), and if ε=1 a penultimate at distance at least four is required in addition to t matched second-layer vertices. Thus t+ε≤K; the displayed bound follows.

If j≥1 then K≤r. Write f(i)=i(k−i−1); f(i)−f(i−1)=k−2i≥1 for 1≤i≤r. Hence f(t)+ε≤f(r) and the claimed rooted traceability cutoff follows from rooted local Ore.
