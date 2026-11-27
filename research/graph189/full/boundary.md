# Traceability through order δ+2σ+1

Let G satisfy Conjecture 189's hypotheses. Then G is traceable for n≤δ+2σ+1. The argument in order-bound.md gives n≤δ+2σ, even using only the distance-two cap. Here take n=δ+2k+1 with k=σ, h=k−δ and the full even-distance hypothesis. Easwar–Johari Theorem B settles G not 2-connected and δ≤2 (then n≤2k+3), so we may take G 2-connected, k≥δ≥3. By the independent-pair count in order-bound.md, α(G)≤k+1.

## Toughness of the cone

Let H be obtained by adding one universal vertex. It is 1-tough, meaning that removing a separating set never creates more components than the size of that set. Indeed, if it failed, the separating set would consist of the universal vertex and some s vertices S of G, with G−S having t≥s+2 components. As G is 2-connected, s≥2. Taking representatives from the components gives t≤α(G)≤k+1, so s≤k−1.

Any component with a vertex of degree at least k has size at least k−s+1, since all neighbors outside it belong to S. At most one component fails this condition, and the degree-δ vertex in it still implies size at least k−s+1−h. Consequently

    n ≥ s + (s+2)(k−s+1) − h.

For 2≤s≤k−2 the quadratic before subtracting h is concave and takes the value 4k−2 at both endpoints, which exceeds 3k+1 for every k≥4. This contradicts n=3k+1−h. The interval is empty when k=3.

For s=k−1, the lower bound is an equality. Each of the t≥k+1 components has at least two vertices except possibly one singleton; thus h≤1. If h=0 there are exactly k+1 pairs. If h=1 there are exactly k pairs and one singleton, which must be the sole low vertex. Every vertex in a pair therefore meets its mate and every vertex of S, as needed for degree k. When present, the singleton also meets every vertex of S to achieve degree k−1. From any paired vertex all vertices in the other components are consequently at distance two. There are at least 2k−1>k of them. This contradiction proves toughness.

## When k−δ≤5

Write N=n+1 for the order of H. Each independent triple in H consists of original vertices, and has degree sum at least δ+2k+3=N+1. The independence number is at most k+1. If there is no independent triple, use the Chvátal–Erdős criterion since H is 2-connected. Otherwise apply Vu Dinh Hoa's circumference bound: a 1-tough graph with independent triple degree sum σ₃≥N and independence number α has a cycle of length at least min{N, N+σ₃/3−α+1}. This gives at least min{N,N+(3−h)/3}, which is strictly greater than N−1 for h≤5. Hence H is Hamiltonian. Removing its universal vertex gives a spanning path in G.

## When k−δ≥5

If α(G)≤k, the Chiba et al. criterion from order-bound.md applies to the cone already at this one-higher order: it has connectivity c≥3 because G is 2-connected, so reducing the α bound by one saves c−2≥1. Thus suppose α(G)=k+1. If any maximum independent set has all pairs at distance two, the theorem in saturated-independent.md supplies the desired path. Otherwise every maximum independent set contains two vertices at distance at least three. Their neighborhoods and the set itself exhaust the order bound with equality. The two degrees are δ and k. As h>0 there is a unique low vertex z, and every maximum independent set contains it. Thus for J=G−z we have α(J)≤k. The order of J is k+k+δ≤3k−5, and its minimum degree is at least k−1.

Suppose J is 2-connected. If there is no independent triple it is Hamiltonian by Chvátal–Erdős. Otherwise its independent triple degree sum is at least 3k−3≥|J|+2. By Bauer, Veldman, Morgana and Schmeichel's Theorem 10, its circumference is at least min{|J|, |J|+σ₃(J)/3−α(J)}≥|J|−1. A spanning cycle of J gives a spanning path in G by following z with one of its neighbors and then traversing the cycle with one edge removed at that neighbor.

In the remaining case, orient a longest cycle C in J and write w for its unique omitted vertex. The set consisting of w and the successors on C of all neighbors of w is independent in J. A successor adjacent to w would insert w into C. If two distinct successors a⁺,b⁺ were adjacent, follow a–w–b, then the reverse arc from b to a⁺, the edge a⁺b⁺, and the forward arc from b⁺ to a. Consecutive neighbors of w were already excluded, so this new cycle contains all of C and w. Thus d_J(w)+1≤α(J)≤k. Since w has degree at least k in G it meets z. Start a path with z,w and enter C through any neighbor of w in J, then traverse the cycle with one edge removed there.

Finally suppose J has a cut vertex v. Since G is 2-connected, J is connected. Every component of J−v has at least k−1 vertices and the whole of J has at most 3k−5, so there are exactly two components. Each has order at most k+δ≤2k−5 and minimum internal degree at least k−2. Such a component is Hamilton-connected: for two prescribed endpoints add a degree-two marker adjacent to them, and complete the original component by Bondy–Chvátal cycle closure since 2(k−2) is at least the augmented order. Each component has neighbors of both z and v, by 2-connectivity of G, and they can be chosen distinct. Otherwise their union would consist of a single attachment vertex whose removal disconnects the rest of that component from G. Take the two Hamilton paths between the chosen distinct attachments in the components and join them through z and v to form a spanning cycle.

**External results.** V. D. Hoa, “A sharp lower bound for the circumference of 1-tough graphs with large degree sums,” Journal of Graph Theory 20 (1995), DOI [10.1002/jgt.3190200204](https://doi.org/10.1002/jgt.3190200204). The +1 refinement is also given in the [Bauer–Broersma–Schmeichel survey, p.5](https://cfc.nankai.edu.cn/_upload/article/files/c6/e1/a2c52bf04b1896f59003b5993582/446d9b25-e3ac-4a8e-a763-04a2cb68565c.pdf). D. Bauer, H. J. Veldman, A. Morgana and E. F. Schmeichel, “Long cycles in graphs with large degree sums,” Discrete Mathematics 79 (1990), Theorem 10. [Primary paper](https://ris.utwente.nl/ws/files/6736746/Bauer90long.pdf). The Chiba et al. and Easwar–Johari references appear in order-bound.md.
