# A minimum-order obstruction from longest cycles after one deletion

Let G be a counterexample to Graph 189, s its vertex connectivity, k its second-smallest degree, h=ceil(k/2), δ its minimum degree and n its order. The solved cases allow 4≤s≤floor(k/2)−2. For k≥25,

    n ≥ s(k−s+2).

At every k in the remaining range we also have

    n ≥ (s+1)(δ−s+2)−1.

In particular as s,k tend to infinity, the known s=O(sqrt(k)) and the first inequality strengthen the necessary order to n≥(1−o(1))sk. Combining with the local geodesic-width upper n≤2k+1+floor(sqrt(k²(k+1)+1)) forces s≤(1+o(1))sqrt(k). All previously derived population bounds can use this stronger lower order. This is an obstruction for hypothetical counterexamples, without any assumption on where the low vertex occurs.

**One deletion.** Delete a minimum-degree vertex z and write H=G−z. Every vertex of H has H-degree at least k−1, and H is (s−1)-connected. Take any longest cycle Q of H. Distance-two witnesses obtained from a two-edge H path between nonadjacent vertices remain at distance exactly two in G. Thus every such count in this argument uses the ambient cap k even if deletion changes longer distances.

If H−Q has an edge, choose a nontrivial component D. Each x∈D has an exterior neighbor y∈D. The cyclic shift argument in longest-cycle-exterior.md applies to xy, now with d_H(x),d_H(y)≥k−1. Specifically, with a_x the cycle neighbor count and q_x=d_D(x), that argument gives k≥a_x+a_y+q_y−q_x≥a_x+k−1−q_x. Therefore q_x≥a_x−1 and q_x+a_x≥k−1, implying q_x≥ceil((k−2)/2). The component contains a cycle of length at least q_min+1≥h: at the start of a longest path in D all its at least q_min neighbors lie on that path, and going to the last of them closes the claimed cycle.

If H−Q is independent, let b count its vertices. Opening Q gives a path in G, so the known longest-path gap gives b≥h+1 (there are b+1 vertices outside Q in G). Each exterior x touches at least k−1 cycle vertices, whose distinct successors are at distance two in G by maximality of Q in H. A cycle contact shared with another exterior vertex gives one further such witness. Hence any fixed cycle vertex has at most two exterior neighbors, since three would give each of the three at least two further even witnesses. Counting contacts gives b(k−1)≤2|Q|=2(n−1−b), hence 2(n−1)≥(h+1)(k+1). This contradicts the upper bound from ../lowblock/geodesic-width-and-order.md at every k≥25. For k=25 the upper bound is 178 while the counting bound gives at least 183. For k≥26, (k−5)²−16(k+1)=k(k−26)+9>16/k², so sqrt(k²(k+1)+1)<k(k−5)/4. Consequently n−1<2k+k(k−5)/4<(h+1)(k+1)/2.

**Cycle theorem.** Nikoghosyan's proven Corollary A states that if a λ-connected graph of order N and minimum degree d satisfies N+2≤(λ+1)(d−λ+2), then outside any longest cycle every cycle has length at most λ−1 (also at most d−λ). See Zh. G. Nikoghosyan, *On Some Versions of Conjectures of Bondy and Jung*, Theorem A and Corollary A, pp. 20–21, https://noad.sci.am/Content/136032/03%20%281%29.pdf. This is the cycle version. The result in the preceding paragraphs gives a cycle of length at least h outside Q. If n+1≤s(k−s+2), apply Corollary A to H with λ=s−1, N=n−1, d≥k−1; it would leave no cycle of length at least s−1 outside Q. Since h≥s−1, this contradicts the constructed cycle. Integrality gives the first bound.

For the second inequality, use G itself. Outside any longest cycle there is a component containing a high vertex with internal degree at least h by longest-cycle-exterior.md. If the unique low lies in this component, remove it for the next count. At least h of the high vertex's internal neighbors except possibly one are high, and every remaining high has internal degree at least h−1 after deletion of the low. A longest path in any nonempty remaining component therefore yields a cycle of length at least h, as above. Thus Corollary A applied to G, λ=s, gives n+2>(s+1)(δ−s+2). This proof does not need k≥25.

When s→∞, let X≤Y count high vertices on the sides of any nonempty partition of the components of G−S. The product XY≤kX+sk² and X≤Y already give X=O(k sqrt(s)). The improved order forces Y≥(1−o(1))sk. Substitution back in the same product gives X≤(1+o(1))k. Greedy grouping as in minimum-cut-populations.md yields a unique giant component, with at most (1+o(1))k high vertices in all other components together.
