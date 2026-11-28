# Small boundary of a large set outside a degree-k vertex's second ball

Under the Graph 189 hypotheses choose any vertex x of degree exactly k. Let A,B,C be its first three layers, with c=|C|, and H the graph induced at distances at least three from x. If c>k, there is y∈B of degree at least k such that U=N(y)∩C satisfies
$$
 |U|\ge k-L,\qquad |N_H(U)\setminus U|\le L-1,\qquad L=4k^2/(c-k).
$$
In particular at n>3k+2 one may take L=4k²/(n−3k−2) whenever that denominator is positive and c>k. The second and fourth layers together have size at most k; a fifth-layer vertex must be the unique low vertex by the upstream diameter and endpoints lemmas, so c≥n−2k−2. The bounds are useful when n/k is large.

Assign C vertices to B-neighbors as in subquadratic-order.md. For each y∈B let f(y) be its load, p(y) its number of A-neighbors, q(y) its number of B-neighbors, and g(y) its number of C-neighbors. Then Σfp≤k² since every anchor sees the assigned vertices of its neighboring columns at distance two. Also Σfq≤2k², since the disjoint loads on each column's B-neighbors lie within distance at most two in C, with at most k at distance one (an A-neighbor sees them at distance two) and at most k at distance two. Any unique low column receives at most k assigned vertices. Thus the total load on high columns is at least c−k. For a high column k−g(y)+p(y)≤2p(y)+q(y), so averaging with the weights f supplies a high column with k−g(y)+p(y)≤L.

Choose any anchor w adjacent to that column. Its positive even-distance cap already counts all g(y) members of U. It consequently misses at most k−g(y) members of A other than itself, since all those misses are at distance two via x. Hence at least |A|−(k−g(y))=g(y) members of A belong to the closed neighborhood of w. At least g(y)−p(y) of them are at distance two from y via w. The root x is one more distance-two vertex from y. Finally every external H-neighbor of U is at distance two from y, since y has precisely U as neighbors in H. These three sets are disjoint, implying |N_H(U) minus U|≤k−g(y)+p(y)−1≤L−1. The order bound on U follows from p(y)≥0. This supplies no bound on the boundary into the earlier layers of G.
