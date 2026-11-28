# Global boundary, dense blocks, and a smaller equivalent graph

Let G satisfy the full connected Graph 189 hypotheses, with order n and second-smallest degree k≥1. Root at any x of degree exactly k. Write A,B,C for the first three distance layers, a=k,b≤k,c=|C|. There is at most one vertex z of degree below k. The existing reduced-target conclusions diameter_le_five and five_endpoints show that vertices beyond C consist of a fourth layer which, together with B, has size at most k, and at most one fifth-layer vertex, necessarily z. Hence n−c≤2k+2.

Assign each vertex of C to one neighboring B vertex and let f(y) be the resulting load. For y∈B put p(y)=|N(y)∩A|, q(y)=|N(y)∩B|, g(y)=|N(y)∩C|. By the previously audited weighted-incidence proof, Σ f p≤k² and Σ f q≤2k². Indeed neighboring loads at an anchor are disjoint C-vertices at distance two. The neighboring loads at a B vertex are C-vertices within distance two, at most k of which are at distance one (use any adjacent anchor) and at most k more at distance two. In particular g(y)≤k. The degree of y is p(y)+q(y)+g(y).

**The full boundary.** Fix a high vertex y∈B, with e=p(y)+q(y), and put U=N(y)∩C. Then
$$
 k-e\le |U|\le k, \qquad |N_G(U)\setminus U|\le k-g(y)+p(y)+q(y)\le 2e.
$$
Choose an anchor w adjacent to y. It sees every member of U at distance two, so it misses at most k−g(y) other anchors through the root. The closed neighborhood of w contains ≥g(y) anchors, of which ≥g(y)−p(y) are at distance two from y. The root is another distance-two vertex from y. A neighbor of U outside U is either y, a B-neighbor of y, or at distance two from y. In the last case it is outside A and different from the root by the layers. Thus the boundary is at most 1+q(y)+k−(g(y)−p(y))−1, as claimed.

Let s≥1 be an integer. Call a column good if y is high and e≤s. The total load on other columns is at most k+3k²/s, by the two weighted sums and the bound k on the sole possible low column. Remove z from every good U if it belongs there to obtain a block W. It has size in [k−s−1,k], outside boundary ≤2s+1, and every member has at least k−2s−1 neighbors inside W.

If two good blocks W,W' intersect, their intersection has size at least k−4s−2: a common vertex has ≥k−2s−1 neighbors in W, of whom at most 2s+1 lie outside W'. If k>6s+3, every vertex of W' has a neighbor in that intersection, as it misses at most 2s+1 members of W' counting itself. Thus W' is contained in the closed neighborhood of W.

Take any maximal family of pairwise disjoint good blocks W_i, i=1,…,t. Every good block lies in the closed neighborhood of a selected one. All C vertices assigned to good columns belong to such blocks except possibly z. Consequently the number of vertices outside the union of selected blocks is at most
$$
 3k+3+3k^2/s+t(2s+1),\qquad t\le n/(k-s-1).
$$

For k≥11s+10 every selected block satisfies the dense-block compression theorem: m≥k−s−1, d≤2s+1 and b'≤2s+1 give m≥2d+3(b'+1)+1. (Equivalently, the sufficient inequality in this calculation is k≥11s+10.) Apply the compression successively. Edges between remaining original vertices outside each compressed block do not change; any new clique edges concern only retained vertices of that same block. Each dummy has no outside adjacency. Thus the size and interior degrees of a later disjoint block do not change and its outside boundary cardinality only decreases. The final graph is traceable exactly when G is, and its order is at most
$$
 3k+3+3k^2/s + (6s+4)\,n/(k-s-1).
$$
Taking s on the order of k sqrt(k/n) yields O(sqrt(nk)) vertices whenever n/k tends to infinity in a sequence of qualifying graphs: the unrestricted n=O(k^{3/2}) bound makes this s tend to infinity, and the numerical compression hypothesis eventually holds. The reduced graph need not satisfy the original parity condition; this is an equivalence for the ordinary spanning path decision problem.
