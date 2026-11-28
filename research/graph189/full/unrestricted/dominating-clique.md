# A sharp order bound for a dominating clique

Let G be a finite connected simple graph with at most k other vertices at positive even distance from each vertex. The argument below also works assuming only the same bound on the exact second neighborhoods. Write n for its order and δ for its minimum degree.

Suppose a vertex x of degree δ has a neighbor c of eccentricity at most two. Every neighbor of c, as well as c itself, belongs to the closed ball of radius two about x. Thus 1+d(c) ≤ 1+δ+|N₂(x)| ≤ 1+δ+k. The ball of radius two about c is the full graph, giving

    n = 1+d(c)+|N₂(c)| ≤ 1+δ+2k.

The same conclusion holds when x is itself such a center, directly from n ≤ 1+δ+k. Under the full even-distance cap, one may subtract from the right side the number of vertices at even distance at least four from x in the neighbor case. Each consumes a separate slot out of x's budget k.

Every member of a dominating clique has eccentricity at most two. A minimum-degree vertex therefore meets one of the two cases above. With k the second-smallest degree, δ ≤ k, so a graph satisfying the conjecture's hypothesis and admitting a dominating clique has n ≤ 3k+1 and is traceable by the branch's independently audited theorem through 3k+2.

In particular, this covers **every chordal graph of diameter at most three**. For completeness, represent a connected chordal graph as the intersection graph of subtrees T_v of a tree, by Gavril's theorem. For each x the union U_x of T_v over v in the closed neighborhood of x is a subtree, since each T_v meets T_x. For x and y at distance at most three there are v in N[x] and w in N[y] equal or adjacent, so U_x meets U_y. A finite pairwise intersecting family of subtrees has a common node: root the tree and choose the deepest among their nodes nearest the root. For any other subtree, a point where it meets the chosen subtree has both nearest nodes on its path to the root. The deeper nearest node thus belongs to both subtrees. The graph vertices whose representing subtrees contain the common node form a clique, and this clique meets every N[x]. It is dominating.

The coefficient and additive constant are sharp for every integer k ≥ 2, even within connected chordal graphs of diameter three. Replace the four vertices of a path, in order, by cliques of sizes 2, k−1, k, k. Join consecutive cliques completely, with no edges between other cliques. Its order is 3k+1. The first two vertices both have degree k, and every other vertex has degree at least k. The positive even-distance vertices from any vertex are precisely the members of the clique two positions away. Their maximum number is k. The two middle cliques together form a dominating clique. Eliminating the outer cliques in succession gives a perfect elimination ordering, verifying chordality directly. A spanning path traverses the four cliques in order.

Gavril, *The intersection graphs of subtrees in trees are exactly the chordal graphs*, J. Combin. Theory Ser. B 16 (1974), 47–56. DOI 10.1016/0095-8956(74)90094-X. The traceability corollary invokes the fork's bounded-order paper proof. The order estimate and extremal construction above use elementary counts.
