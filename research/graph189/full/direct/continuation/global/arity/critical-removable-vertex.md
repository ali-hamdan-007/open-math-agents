# Traceability at arbitrary fixed connectivity and large degree

Let G be a finite connected qualifying Graph 189 graph, k its second-smallest degree and s its vertex-connectivity. If s≥5 and

    k ≥ 6s²+10s−6,

then G has a Hamiltonian path. The maximum degree and the unique possible low degree are unrestricted. Thus in a counterexample sequence with growing k and s≥5, one necessarily has liminf s/sqrt(k)≥1/sqrt(6). Together with the previously proved upper order bridge and order cap, the remaining growing-connectivity range is confined between positive constant multiples of sqrt(k).

Suppose G is a counterexample. The order theorem arbitrary-cut-high-order.md allows us to assume

    n < (s+3/2)k+2s+2.             (1)

If a minimum-degree vertex belongs to no minimum cut, root/universal-minimum-order.md provides n≥(s+2)(k−s+1)−1. This already exceeds (1) in the assumed range. Hence take a minimum-degree vertex z on a minimum cut. If z has degree k then δ(G)=k. Otherwise it is the only low vertex. Select one high z-neighbor in each of two distinct components of the complement of the cut; each component touches z by minimality and every vertex off the cut is high. Each chosen vertex has at least k−s+1 members in its closed internal neighborhood. All of these are either z-neighbors or at exact distance two from z. The two neighborhoods are disjoint. The even cap thus gives

    δ(G) ≥ k−2s+2.

A finite critically s-connected graph has minimum degree at most 3s/2−1 (Lick and collaborators; Mader). Equivalently, a graph of connectivity s and minimum degree exceeding this bound has a vertex w whose deletion leaves an s-connected graph. The present δ(G) bound exceeds 3s/2−1, so choose such a vertex w, not necessarily a minimum-degree vertex. Form K by adding edges from w to all other vertices. It has κ(K)≥s+1 because K−w=G−w is s-connected, and δ(K)≥k−2s+2. The critical-connectivity result is Theorem 1(b) of M. Stein's survey on vertex-minimal connectivity (linked below).

Write H=G−w, of minimum degree at least k−2s+1; all but possibly one of its vertices have H-degree ≥k−1. Every longest cycle of K uses w and consists of w and a longest path P of H. If H−P has a nontrivial component, write a_x and q_x for the neighbors on P and in that component of a member x. For a neighbor y in the component, the usual longest-path shifts and contact witnesses in root/universal-minimum-order.md, all measured in the original G, give

    k ≥ a_x+a_y+q_y−q_x ≥ a_x+k−2s+1−q_x.

Since q_x+a_x≥k−2s+1, this yields q_x≥ceil((k−4s+2)/2). Every member of the nontrivial component satisfies it, so a longest path within it gives a cycle of order at least q_min+1≥s+1. Nikoghosyan's Corollary A, applied to K with λ=s+1 as in root/universal-minimum-order.md, therefore yields

    n ≥ (s+2)(k−3s+3)−1 = (s+2)k−3s²−3s+5.

This is at least (s+3/2)k+2s+2 under the displayed degree hypothesis, contradicting (1). The even-distance condition is applied only within the original graph G.

If H−P is independent, the known path gap in G ensures at least ceil(k/2)+1 vertices in H−P: P also misses w. At least ceil(k/2) are high. Each has at least k−1 contacts on P and therefore at least k−1 distinct successor witnesses at exact distance two. A path vertex consequently cannot touch three high exterior vertices, since the other two would give each a pair of extra external even witnesses. Thus (k/2)(k−1)≤2|P|≤2n. This contradicts (1), since k(k−1)/4≥(s+3/2)k+2s+2 throughout k≥6s²+10s−6, s≥5. The theorem follows.

The finite critical-connectivity theorem is reproduced in M. Stein, *Ends and vertices of small degree in infinite minimally k-(edge)-connected graphs*, Theorem 1(b), with original references to Chartrand–Kaugars–Lick and Mader. https://www.math.uni-hamburg.de/home/diestel/papers/others/minim.pdf

The external cycle theorem is Zh. G. Nikoghosyan, *On Some Versions of Conjectures of Bondy and Jung*, Theorem A and Corollary A, pp. 20–21. https://noad.sci.am/Content/136032/03%20%281%29.pdf
