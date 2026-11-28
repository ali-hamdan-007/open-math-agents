# Routed neighborhoods and larger Hamilton-connected blocks

Consider the usual optimized longest path P of a hypothetical qualifying graph without a spanning path. Let C be its smallest high-bearing exterior component, x a high noncut vertex of C, q=d_C(x), H=N_C[x], R the vertices of C at ambient distance two from x, and r=|R|. Let H* be H without the possible low member, l=|H|−|H*|. The local exterior results give r≤2q−k+1 and minimum degree at least k−q−l in H*. The latter follows from the distinct path witnesses for x and its high neighbors, as in ../../global/two-thirds-exterior-degree.md. Write J for the largest matching from H* to P.

For any connected graph on at least three vertices with a universal vertex x and minimum degree d, any two distinct prescribed vertices u,v are joined by a path of order at least d+1. If u,v differ from x, take a longest path starting at u in the graph with x and v deleted. Its terminal has degree at least d−2 there. Append x and v at that terminal. If one terminal is x, take a longest rooted path from the other in the graph with x deleted and append x. In particular

    n ≥ |C| + J + (J+1)(k−q−l+1).

Indeed x is universal in H*, and the prescribed-terminal routes apply to the J−1 inner gaps and both tails on P, each of which could be replaced by its H* route if shorter. This estimate is valid even when H* has several blocks and the degree-sum condition for Hamilton-connectedness fails. For example, the join of a K₂ with two disjoint copies of K_{d−1} has minimum degree d and two universal vertices, but a path between those universal vertices contains at most d+1 vertices. The elementary rooted route is degree-sharp.

Suppose B contains x as in k14-k15.md, either an endblock with all noncut vertices high, or C itself when 2-connected. Assume q is the minimum degree of good vertices within B, exempting the endblock articulation or a possible low vertex, and choose I to be B outside H, R and the exception. If I is nonempty, its vertices have degree at least q−r−1 within I. Thus a path beginning at an I vertex contains at least q−r vertices when this is positive. For a matched v∈H*, connect H*−v to I in B−v, trimming the route to the last H* member and first I member. There is at least one intermediary since H and I have no edges. The guaranteed prescribed H* route can finish at that last H* member before the connector and the path within I. Consequently the preceding lower bound gains at least 2(q−r+1) from its two tails. It gains a further two if the exception is absent from I and from B outside H∪R. This tail improvement also applies when H* is too sparse to be Hamilton-connected.

## An expansion test using the cover of H*-to-P contacts

Choose a minimum bipartite cover with marked part M⊆P and interior part Y⊆H*, so p=|M|, u=|Y| and p+u=J. Put W=H*−Y, w=|W|, and let a=q+r+p−k. Every W vertex is high and has all its C neighbors in H∪R and all its path contacts in M. It therefore misses at most a edges across the other q+r members of H∪R and the p marks. Thus whenever W is nonempty a≥0, and there are at most wa missing edges from W to any disjoint subset of H∪R.

Write V₀=H*∪(R∩B) and N=|V₀|. Suppose an integer L with w≤L≤N has

    D=ceil((L+1)/2) ≤ w,     L≥2a+3,
    N−floor(wa/(w−D+1)) ≥ L.

Then B contains a Hamilton-connected induced subgraph of order L containing W. A member of V₀−W with fewer than D W neighbors is missing at least w−D+1 of these edges. The last hypothesis leaves at least L vertices after discarding all such members, and all W survive. Take precisely L of the survivors including W. All W vertices have degree at least L−1−a≥D, and each remaining vertex has degree at least D because W is retained. The usual endpoint-marker closure now yields Hamilton-connectedness. When L<w and the induced W has L≥2a+3, any L-subset of W already suffices.

For any Hamilton-connected K produced by this test in B and |K|≥s=κ, Menger supplies s disjoint links to P. The basic count is n≥|C|+s+(s+1)|K|. If B−K is nonempty it gains at least two: any connector with an internal vertex contributes to both bordering gaps, while if all are direct each outer connector can traverse K and add a B vertex because B−v is connected. If B−K contains a set of minimum internal degree at least one and each outer direct link can be extended through that set, then the guaranteed gain is at least three for s≥2. Indeed two units of connector interior give four gains; a single interior vertex leaves at least one outer link direct and extendible; and when all are direct both tails gain at least two. These estimates are strongest when there are too few distinct H*-contacts to obtain s direct links to K without Menger.

For instance, when q≤(1−η)k for some fixed η>0, the first bound and the geodesic order estimate immediately give J=O(sqrt(k)/η). This exhibits a small set of marked and H* vertices covering the H*-contacts throughout that range of degrees; it does not require q≤2k/3. The expansion test then expresses the additional density of the uncovered H* vertices inside their distance-two neighborhood by an explicit finite inequality.
