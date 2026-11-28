# Restoring the lost degree by making one vertex universal

Every hypothetical counterexample G to Graph 189, with second-smallest degree k and connectivity s, has order

    n ≥ (s+1)(k−s+2)−1.

The bound permits an arbitrarily low minimum degree. If a minimum-degree vertex belongs to no minimum cut, a further improvement is

    n ≥ (s+2)(k−s+1)−1.

This strengthens the order estimate obtained by deleting the minimum-degree vertex alone. It relies on the audited connectivity bound 3s<k from ../sep/cover/third-connectivity.md. The previously audited low-degree results suffice for all small or degenerate cycle lengths below.

Choose a minimum-degree vertex z. Form K on the original vertex set by making z universal. Every other vertex originally has degree at least k and retains all its edges, so δ(K)≥k. Also κ(K)≥s. Any longest cycle of K contains z, which could otherwise be inserted on a cycle edge. Deleting z from this cycle gives a longest path P in the unchanged induced graph H=G−z, since any longer path in H could be closed via z. All vertices of H have H-degree at least k−1. The even-distance hypothesis is only applied to G below.

If an exterior component D of H−P contains an edge, every vertex x of D has an exterior neighbor y. Let a_x and q_x count its neighbors on P and within D. The shifted contacts on a longest path avoid the endpoints and consecutive contact pairs. Exactly as in longest-cycle-exterior.md, the successors and predecessors of x's contacts, contacts of y missed by x, and the new exterior neighbors of y give k≥a_x+a_y+q_y−q_x. In detail, each shared contact of x and y contributes a distinct successor outside the predecessor set: a shared index i and another x contact two steps later permit replacing that two-edge segment by the length-three detour through y,x. Every distance-two witness found in induced H is still at distance two in G. As a_y+q_y≥k−1, this gives q_x≥a_x−1, hence q_x≥ceil((k−2)/2). The component therefore contains a cycle of length at least h=ceil(k/2), by closing a longest path at its first vertex's furthest neighbor.

An independent exterior is impossible. The real path P in G misses z and b exterior vertices, so b≥h+1 by the gap theorem. An isolated exterior x in H−P has a=d_H(x)≥k−1 contacts on P. They avoid the endpoints, since otherwise P extends, and they have no consecutive pair, since otherwise x can be inserted. On the linearly indexed path the predecessor set and successor set of the contacts have the same cardinality a and different least indices. Their union therefore has at least a+1 elements, all on P at distance exactly two from x in G. The cap forces a=k−1, and saturates the even-distance allowance. Since d_G(x)≥k, x is adjacent to z. Any two such isolated exterior vertices would be at distance exactly two via z as well, an additional witness off P. Hence at most one exterior vertex is isolated, contradicting b≥h+1 when the exterior is independent.

Apply Nikoghosyan's cycle Corollary A to K with λ=s. If n+2≤(s+1)(δ(K)−s+2), no longest cycle can omit a cycle of length at least s. The cycle in D has length ≥h≥s. Thus

    n ≥ (s+1)(δ(K)−s+2)−1.

If z belongs to no minimum separator, H is s-connected and K is (s+1)-connected. The same argument with λ=s+1 applies since 3s<k and s≥2 imply h≥s+1. If z does belong to a minimum separator, its choice yields wholly high sides on deleting that separator when z is the unique low vertex.

These conclusions also permit δ(K)≥k+1 if no degree-k vertex other than z is adjacent to z in G: every such vertex gains the missing edge to z. The universal vertex itself has degree n−1, and the counterexample regime has n≥k+2. When all vertices of G are high, the same argument can choose any z. In the narrow band n<(s+1)(k−s+3)−1, every vertex must then have a degree-k neighbor. No parity claim is made about the artificial edges of K.

Source for the cycle statement: Zh. G. Nikoghosyan, *On Some Versions of Conjectures of Bondy and Jung*, Theorem A and Corollary A, pp. 20–21, https://noad.sci.am/Content/136032/03%20%281%29.pdf.
