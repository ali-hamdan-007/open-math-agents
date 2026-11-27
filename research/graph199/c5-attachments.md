# Graph199 triangle-free attachments to an induced five-cycle

Write k=κ(G)≥3 and assume G is triangle-free with t(G)≤k+2, where t is the largest induced tree order. Every vertex has degree k or k+1, because connectivity gives the lower bound and each neighborhood induces a star together with its center. Number the vertices of an induced five-cycle c₀,…,c₄ cyclically, with indices modulo five.

## All off-cycle vertices have two cycle neighbors

**Proposition.** If every off-cycle vertex has two cycle neighbors, then α(G)≤k+1. Thus this branch of the exact Graph199 H2 is empty.

Partition V(G) into A₀,…,A₄, where Aᵢ contains cᵢ and all off-cycle vertices whose two cycle neighbors are cᵢ₋₁,cᵢ₊₁. These are the only possible independent two-subsets of the cycle. Triangle-freeness implies that any edge joins consecutive roles, since two vertices from equal or nonconsecutive roles share a cycle neighbor. Each cᵢ is complete to its two consecutive roles by their definition. Accordingly, for x∈Aᵢ the total possible number of neighbors is d(cᵢ)≤k+1, and x has degree at least k. The edges missing from the complete cyclic blow-up therefore form a matching.

For any distinct nonconsecutive roles Aᵢ and Aⱼ, take the length-three arc between cᵢ and cⱼ, and replace its endpoints with the full sets Aᵢ and Aⱼ. There is no edge within or between these two endpoint sets. The two internal cycle vertices are adjacent, and each is complete to one endpoint set and anticomplete to the other. The resulting induced double star gives |Aᵢ|+|Aⱼ|+2≤k+2. In particular, each |Aᵢ|≤k−1 since every other role is nonempty.

An independent set occupying no consecutive roles meets at most two roles and has order at most k by the double-star bound. When it occupies consecutive roles Aᵢ,Aᵢ₊₁, it contains exactly one vertex from each because every vertex misses at most one eligible neighbor. Those two vertices cannot miss another eligible neighbor, so the independent set misses the two flanking roles Aᵢ₋₁ and Aᵢ₊₂. Its size is at most 2+|Aᵢ₊₃|≤k+1.

## General attachment constraints

**Square matching.** For any edge uv, let A=N(u) minus v and B=N(v) minus u. These are disjoint independent sets. If J is an independent set in G[A∪B], adjoining u and v gives an induced double star of order |J|+2, hence α(G[A∪B])≤k. By König's theorem, G[A∪B] has a matching of size at least |A|+|B|−k. Each matched edge gives an induced square through uv, with distinct other vertices. This matching misses at most k−|B|≤1 vertices of A and at most k−|A|≤1 vertices of B. In particular it covers all of A if d(v)=k+1 and all of B if d(u)=k+1. Consequently any distance-two pair with only one common neighbor consists of degree-k endpoints: for a path x−y−z, if d(x)=k+1 then the matching for xy must cover z in N(y) minus x, giving another common neighbor. Swap x,z for the other endpoint.

**Pentagon matching for a length-two path.** For a path u−v−w set A=N(u) minus N(w), B=N(w) minus N(u). These are disjoint independent sets anticomplete to v. Every independent subset of A∪B extends the path as leaves, so it has at most k−1 elements. The bipartite graph on A,B has a matching of size at least |A|+|B|−(k−1). Each match gives an induced pentagon through u−v−w, with disjoint pairs of added vertices. This gives a quantitative form of the pentagon-free private-neighborhood argument.

**Independent off-cycle set.** If J⊆V(G) minus V(C) is independent, let j₁,j₂ count its vertices having respectively one and two cycle neighbors. For each cycle vertex cᵣ, the four-vertex path C minus cᵣ admits as independent leaves the members of J with exactly one remaining cycle neighbor. There are at most k−2 such vertices. Summing over r gives 4j₁+2j₂≤5(k−2). This bound does not charge vertices having no cycle neighbor.

These conditions leave open the exact triangle-free branch at arbitrary k when every induced pentagon has a vertex with zero or one neighbor on that pentagon. The separate κ=3 and bipartite proofs are in `bipartite.md`.

## At most one exception to the two-neighbor condition

**Stronger proposition.** The same bound α(G)≤k+1 holds if at most one off-cycle vertex has fewer than two cycle neighbors.

Let E be the exceptional set of vertices and omit E from the five roles. The same induced double stars bound nonconsecutive role sums by k. Let I be independent, j=|I∩E|, r=|E|, m=r−j+1, and let bᵢ=|I∩Aᵢ|. Each role vertex in I misses at most m eligible role neighbors: its total eligible role-neighbor count is at most d(cᵢ)≤k+1, its degree is at least k, and at most r−j exceptional vertices can be its neighbors. If bᵢ and bᵢ₊₁ are positive, then bᵢ,bᵢ₊₁≤m and Aᵢ,Aᵢ₊₁ each contain one extra vertex, namely their unselected cycle representatives. If bᵢ>0 then bᵢ₋₁+bᵢ₊₁≤m.

If no occupied roles are consecutive, |I|≤k+j≤k+r. If an occupied consecutive pair is in no occupied triple, the only other possibly occupied role is the opposite Aᵢ₊₃. Its size is at most k−max{bᵢ,bᵢ₊₁}−1 by the role-sum bound against both Aᵢ and Aᵢ₊₁. Thus |I|≤k+min{bᵢ,bᵢ₊₁}−1+j≤k+r. When the occupied roles form a run of three or four, the inequalities bᵢ₋₁+bᵢ₊₁≤m at the occupied roles bound the role contribution by 2m. For all five occupied, summing the inequalities bounds it by floor(5m/2). In particular for arbitrary r these arguments give α(G)≤max{k+r, floor(5(r+1)/2)}.

For r≤1 this yields α≤k+1 except possibly when k=3, r=1, j=0 and all five roles are occupied. This exception forces each bᵢ=1, and each selected vertex excludes its role's representative, so every role has size at least two. Since each representative has degree at most four, all roles have size two. The exceptional vertex x sees no cycle representative, whose four role neighbors already exhaust its degree bound. Each of the five selected vertices misses both selected vertices in the consecutive roles and has at most two role neighbors. Hence each must see x to have degree at least three. This gives d(x)≥5, a contradiction.

The exact nonbipartite triangle-free branch can therefore be narrowed to graphs in which **every** induced pentagon has at least two outside vertices with at most one cycle neighbor.
