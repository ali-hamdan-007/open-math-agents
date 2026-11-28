# Traceability of cocomparability graphs under the Graph 189 degree and distance bounds

Every finite connected cocomparability graph satisfying the hypotheses of Graph 189 has a Hamiltonian path. In the 2-connected case it suffices that every vertex has at most k vertices at distance exactly two and at most one vertex has degree below k. In particular the assertion holds for interval graphs.

We first prove that in the 2-connected case c(G−S)≤|S|+1 for every S under the stated distance-two and degree conditions.

Suppose S is inclusion-minimal with c=c(G−S)≥s+2 where s=|S|. By 2-connectivity s≥2. Each component of G−S has neighbors in at least two distinct vertices of S. Call an element of S an anchor and write T(C) for the anchors touching a component C. For proper T⊊S, at most |T| components satisfy T(C)⊆T. Indeed, deleting T would leave all such components and at least one further component containing a surviving anchor. Minimality bounds their total by |T|+1.

Take a high vertex x (degree ≥k) in C with r≥1 anchor neighbors forming the set Q. At least c−(s−r) components touch Q, by the preceding bound with T=S−Q. Hence at least r+1 other components each contain a distance-two vertex from x. If an anchor adjacent to x is complete to another component D, these witnesses can include every vertex of D, increasing their number to at least r+|D|. Since

    r+|D| ≤ k ≤ deg(x) ≤ r+|C|−1,

we have |D|<|C|. This proves that one anchor cannot be complete to two distinct components that both contain a high vertex. At most one component contains no high vertex, and this component is necessarily the singleton comprising the unique low vertex.

For a cocomparability graph, use a poset whose incomparability graph is G. Two different components of G−S compare in a uniform direction in the poset. To see this, comparability with a fixed outside element cannot change direction across an incomparability edge within a component, and each component is connected. Apply this observation on both sides. The components consequently form a strict total order C1,...,Cc. An anchor touching a component before Ci and a component after Ci is complete to Ci. In fact, any comparison between the anchor and any vertex of Ci would produce by transitivity a comparison with one of those two neighbors of the anchor. In an interval graph the same property follows by ordering the disjoint component interval unions from left to right.

Every interior Ci is strictly spanned by an anchor, meaning an anchor touches some component on either side of it. Otherwise split S into L, consisting of the anchors meeting some component before Ci, and R=S−L. Both parts are nonempty and proper since both sides of Ci exist and no vertex touches both sides. Every component left of Ci has its entire anchor set in L, and every component right of Ci has its entire anchor set in R. Minimality gives c−1≤|L|+|R|=s, impossible.

Let H be the set of interior components containing at least one high vertex, with h=|H|. Choose for each of them an anchor strictly spanning it. The h chosen anchors are distinct by the component-size inequality. At most one chosen anchor touches C1. Indeed, a representative of any high interior after the first would, if it touched C1, also strictly span the first. The same argument holds at Cc. As each extreme touches at least two anchors, each must touch an anchor outside the h representatives.

We have h≥c−3≥s−1. If h≥s then no spare anchor exists, a contradiction. Otherwise h=s−1 and a single spare anchor must touch both extremes. It strictly spans every high interior, so h≤1. Since s≥2, equality forces s=2,h=1,c=4. The two interior components are thus a low singleton z and a high-containing H. Both anchors touch both extremes, and hence both are complete to z and H. From z all vertices of H and one vertex in each extreme are at distance exactly two. Thus k≥|H|+2. A high vertex of H has degree at most |H|−1+2=|H|+1, impossible.


Now add a universal vertex u to G, obtaining J. The same poset with u incomparable to every original element represents J as a cocomparability graph. If deleting T disconnects J, then u belongs to T. Put S=T−{u}. The separator inequality gives c(J−T)=c(G−S)≤|S|+1=|T|. Thus J is 1-tough. The theorem of Deogun, Kratsch and Steiner gives a Hamiltonian cycle of J. Deleting u from the cycle produces a Hamiltonian path of G.

For a connected graph on at least two vertices, the assumption that at most one vertex has degree below k gives k≤d₂, its second-smallest degree. Under Graph 189's positive-even-distance bound, each even-distance set including the root therefore has at most d₂+1 vertices. In the non-2-connected case Theorem B(4) of Easwar and Johari yields a Hamiltonian path directly. A graph of order one has the one-vertex spanning path.

- Jitender S. Deogun, Dieter Kratsch and George Steiner, “1-Tough cocomparability graphs are hamiltonian,” Discrete Mathematics 170 (1997), 99–106. https://doi.org/10.1016/0012-365X(95)00359-5
- Rohun Easwar and Shaurya Johari, “Conditions for traceability under a bound on the size of even-distance sets,” Theorem B(4), arXiv:2609.11719 (2026). https://arxiv.org/abs/2609.11719
