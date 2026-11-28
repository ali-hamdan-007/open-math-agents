# A Hamiltonian path after deleting the minimum vertex

Write k for the second-smallest degree, δ for the minimum degree at z, and s for vertex connectivity. Assume the original even-distance cap. Suppose the graph has no Hamiltonian path, and deleting z leaves a Hamiltonian path.

Choose a longest path Q among paths containing z. For an exterior vertex a write A for its contact positions on Q. Its predecessors and the successor of its final contact give |A|+1 distinct distance-two witnesses if A is nonempty. Endpoint extension and consecutive insertion preserve z. For an exterior edge ab with respective contact sets A and B, charge the predecessors of A, the successors of A∩B and B∖A. All charges are distance-two witnesses of a. The first two families can overlap only at the position of z, since any length-two contact gap closed by a,b would otherwise increase the path while retaining z. The last family is disjoint from both. Hence at least |A|+|B|−1 distinct path vertices are charged. Adding the neighbors of b outside Q that are distinct from a and nonadjacent to a gives

    |A| + deg(b) ≤ k + 1 + |N(a)∖Q|.

All vertices outside Q are high. The strict single shift excludes an isolated exterior vertex. The displayed inequality then gives |N(a)∖Q|≥floor(k/2) for each exterior a. Consequently every path containing z omits at least floor(k/2)+1 vertices.

On the Hamiltonian path of G−z, each two successive z contacts bound an open interval, and there are two outer tails. Replacing any one of these intervals or tails with z produces a path through z. All δ+1 of them therefore have length at least floor(k/2)+1. Adding the δ marks and z gives

    n ≥ (δ+1)(floor(k/2)+2).

In particular if δ≥2λ+1 the graph has the full numerical bound n≥(λ+1)(k−λ+2)−1 directly, including when its universal completion at z has a Hamiltonian cycle. Taking λ=s and s+1 gives both structural inputs when δ≥2s+3.

For a longest path Q containing z, write m for the total number of omitted vertices and u=k+1−m. The same tail-and-gap argument gives (δ+1)(m+1)≤n. The minimum-root layer cover gives n≤1+δ+k+δ(k+1−δ), since the single vertex branch forces 2δ≤k. It follows that m≤k+1−δ, hence 2floor(k/2)≥m+1 when δ≥3. The induced graph on the complement of Q therefore has a Hamiltonian path for every two distinct prescribed endpoints.

For m>u the uniform-mark conclusion admits a shorter Hall argument. A matching of g distinct exterior vertices to path positions forces g(m+1)≤|Q|. Orient each matched position to the left if it precedes z and to the right otherwise. Take the position itself and m additional positions in that direction. The tails have room, and intervals assigned on the same side are disjoint since their distinct exterior contacts have a spanning connection, which would improve Q without losing z. The small-root order bound sharpens to n≤m+u+δ+mu via (m−δ)(u−δ)≥0, so g≤u. Every exterior vertex has at least u real contacts. If their union contained at least u+1 positions, Hall’s deficiency theorem would give a matching of size u+1. In fact the union of every nonempty proper subset of the m vertices has size at least u, and the whole set has at least u+1, exactly the required deficiency inequalities. Thus the union is a common set of exactly u positions. All exterior vertices also have to be adjacent internally to every other one. This covers every even k and all but m=(k+1)/2 for odd k. The equal-interval exchange in all-near-spanning.md handles the resulting clique on paper.

The Lean source and axiom logs carry independent scopes. Graph189RootedSplice and Graph189RootedColumns establish the path surgery and charged positions. Graph189RootedOmission establishes both the internal degree and the all-paths-through-z omission. Graph189SmallMinimumOrder, Graph189RootedHamiltonConnected, Graph189RootedMatchedOrder and Graph189NearUniform contain the subsequent graph interfaces. Graph189HighDegreeNearTrace links the numerical orders to the structural traceability theorem. Consult each module's log and compiled output before attributing kernel verification to it.
