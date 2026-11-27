# Traceability through order 3k−2

Let G be connected and satisfy the even-distance condition of Graph Conjecture 189, with n=|G| and second-smallest degree k. Then G is traceable whenever n≤3k−2.

**Setup.** Easwar–Johari's Theorem B covers n≤2k+3 and graphs that are not 2-connected. We may thus assume G is 2-connected, n≥2k+4 and k≥6. The previously proved Chiba et al. cone argument covers n≤δ+2k. Hence we may suppose δ<k−1, and write z for the unique low vertex. Set J=G−z, N=n−1, so J is connected, 2k+3≤N≤3k−3 and every vertex of J has degree at least k−1 in J.

If J has an independent set of size k+1, its members are high in G. Any two members at distance greater than two in G would have two disjoint neighborhoods each of size at least k, disjoint also from the independent set, implying n≥3k+1. Thus all its pairs have distance two in G and the previously established saturated-independent-set theorem gives a spanning path. We can now assume α(J)≤k. Every witnessed two-edge path between nonadjacent vertices of J is also a distance-two witness in G.

## One-toughness when J is 2-connected

If J were not 1-tough, a cut S of size s≥2 would leave t≥s+1 components. Representatives from distinct components form an independent set in J, so t≤k and s≤k−1. Each component has order at least k−s, since a vertex can have at most s neighbors outside its component. In particular,

    N ≥ s+(s+1)(k−s).

For 3≤s≤k−3, this quadratic is concave and both endpoint values are 4k−9. This exceeds 3k−3 when k≥7. If k=6 and s=3, equality forces four components of order three. Every vertex there sees every member of S to reach degree five. A vertex in one triple has all nine members of the others at distance two in G, impossible.

For s=2, the graph outside S has at most 3k−5 vertices, and there are at least three components of size at least k−2. As k≥6, there are exactly three, with at most one extra vertex in total. A vertex in a size-(k−2) component sees both members of S. Every vertex in either other component has some neighbor in S, since the internal maximum degree is at most k−2. Consequently at least 2(k−2)>k vertices are at distance two from the first vertex.

For s=k−2, there are at least k−1 components of size at least two, with at most 2k−1 total vertices outside S. There are exactly k−1 components with at most one extra vertex. A vertex in a size-two component sees every member of S. Every other component vertex is adjacent to some member of S since its component has size at most three. This supplies at least 2(k−2)>k distance-two witnesses.

For s=k−1, t=k, and the total order outside S is at most 2k−2. A singleton exists and its vertex x sees every member of S. In every other singleton x sees its vertex at distance two. Every nonsingleton component contributes at least two such vertices: if all its edges to S left from a single vertex, that vertex would disconnect the rest of the component from J, contradicting 2-connectivity. If there were two nonsingleton components, x would see at least k+1 vertices at distance two. If all components are singletons, n=2k. If there is just one nonsingleton component of size r, then r≤k−1; each of its vertices must see S for degree at least k−1. Now x has k−2+r distance-two witnesses, whence r≤2 and n≤2k+1. The last two orders were excluded at setup. This proves 1-toughness of J.

Use Vu Dinh Hoa's 1995 circumference bound for 1-tough graphs of order N≥3 and independent-triple degree sum σ₃≥N:

    c(J) ≥ min{N, N+σ₃(J)/3−α(J)+1}.

Here σ₃(J)≥3(k−1)≥N and α(J)≤k, giving c(J)=N. When no independent triple exists, Chvátal–Erdős gives Hamiltonicity directly from 2-connectivity. Opening the cycle at a neighbor of z and prefixing z yields a Hamilton path in G.

## When J has a cutvertex

Let v be a cutvertex. Each component of J−v has minimum internal degree at least k−2 and hence order at least k−1. Since |J−v|≤3k−4<3(k−1), there are exactly two components. Denote their orders by b≥a. The smaller order satisfies a≤(3k−4)/2≤2k−5, so its minimum degree gives all nonadjacent degree sums at least a+1. It is Hamilton-connected by the endpoint form of Ore's theorem, also obtainable by adding a degree-two endpoint marker and using ordinary cycle closure.

The larger order is at most 2k−3. If b=2k−3 then a=k−1. Every vertex in the smaller component must see both v and z, since its degree in G is at least k and at most k−2 of its neighbors lie inside that component. This forces δ≥k−1, contrary to setup (or directly invokes the already settled δ+2k bound).

If b≤2k−4, the larger component has minimum internal degree k−2≥b/2. By Dirac's theorem it has a spanning cycle. Choose one of its vertices adjacent to v, and open that cycle so the resulting spanning path ends there. In the smaller component take a v-neighbor and a distinct z-neighbor. These attachment sets are nonempty by connectivity of J and G−v respectively. If distinct choices were impossible, the sole attachment vertex would disconnect the rest of the smaller component from G; its order is at least k−1≥2. Traverse the larger path, then v, the smaller spanning path between the chosen attachments, and finally z. This uses both components, v and z exactly once. It does not require the larger component to be Hamilton-connected.

## Sources and scope

The proof is handwritten. It uses the saturated independent-set and δ+2k theorems audited in boundary-audit.md. The 1-tough circumference result was checked in the original publisher's abstract of V. D. Hoa, Journal of Graph Theory 20 (1995), 137–140, DOI https://doi.org/10.1002/jgt.3190200204. Easwar–Johari Theorem B appears in https://arxiv.org/abs/2609.11719. The final argument also uses the classical Dirac minimum-degree and Ore Hamilton-connected bounds.
