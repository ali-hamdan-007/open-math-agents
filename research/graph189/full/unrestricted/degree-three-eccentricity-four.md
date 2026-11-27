# A degree-three vertex in the high-order residual has eccentricity three

Assume the hypotheses of `degree-three-two-anchor-order.md`, with G 2-connected and n>3k+2. That result shows that eccentricity at least four at z forces the following unique template. The three anchors A={a₁,a₂,a₃} induce a triangle. The second layer consists of k−1 ports: a uniquely private pᵢ adjacent only to aᵢ among the anchors, for each i, and a set W of k−4 ports adjacent to all three anchors. There is a single fourth-layer vertex y and no fifth layer. We show this template impossible. This argument adapts the degree-three three-private-port count to the extra vertex y.

Write C=L₃ and c=|C|=n−(1+3+(k−1)+1)=n−k−4≥2k−1. Let Vᵢ be the set of vertices of C at distance two from aᵢ. Every C vertex belongs to at least one Vᵢ via its preceding port. An aᵢ–C path of length two must use a port as its interior vertex: neither z nor another anchor touches C. Define Uᵢ to consist of those belonging only to Vᵢ, set U=U₁∪U₂∪U₃, and let B=V₁∩V₂∩V₃. The two foreign private ports have distance two from aᵢ via the triangle, so |Vᵢ|≤k−2. Nonexclusive vertices each contribute at least two memberships. Consequently

    |U|≥2c−Σᵢ |Vᵢ|≥k+4.

Every w∈W sees at most one of p₁,p₂,p₃. If w saw all three, it would see at distance two every exclusive vertex (which sees only its own private port among the second layer), as well as z. If w saw exactly two and missed pᵢ, then each vertex of C outside Uᵢ∪B has a neighboring private port other than pᵢ. Indeed it is visible to a foreign anchor, and cannot see W because it is not triple-visible. These vertices miss w, so all are at distance two from w. Also z and pᵢ have distance two from w, via aᵢ. This would give

    c≤k−2+|Uᵢ|+|B|≤k−2+|Vᵢ|≤2k−4,

contrary to c≥2k−1.

For each i let Rᵢ=N(pᵢ)∩C and let Dᵢ consist of the C vertices outside Rᵢ having a neighbor in Rᵢ. Put bᵢ=|N(pᵢ)∩W|. All Dᵢ lie at distance two from pᵢ. In three disjoint further sets it sees |W|−bᵢ missed common ports, z, and both foreign anchors at distance two via aᵢ. Hence

    |Dᵢ|≤k−(|W|−bᵢ)−3=bᵢ+1,
    Σᵢ |Dᵢ|≤|W|+3=k−1.

The second inequality uses the fact just proved that each w∈W touches at most one private.

For every x∈Uᵢ all its neighbors outside C lie in {pᵢ,y}. Its closed neighborhood within C therefore has size at least k−1. Since |Vᵢ|≤k−2, it has a C-neighbor u outside Vᵢ. Such a u has a port neighbor, lies outside the triple-visible set, and misses pᵢ. It therefore sees a private pⱼ with j≠i. Since x sees no such pⱼ, x belongs to Dⱼ. We obtain

    k+4≤|U|≤Σᵢ |Dᵢ|≤k−1,

a contradiction. Eccentricity at most two gives n≤k+4 directly, so the only remaining eccentricity at z is three. This is a metric and incidence reduction for unrestricted orders in the high-order degree-three problem.
