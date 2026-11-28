# A block-tree-free reduction of the cut-vertex case

Let G be connected, let k denote its second-smallest degree, and assume every vertex has at most k other vertices at positive even distance. Assume n ≥ 2k+3. A side at a gate c is a nonempty set S disjoint from c such that an edge from S to its complement must end at c. Every component of G−c is a side.

For a contact x∈S adjacent to c and any y∉S, d(x,y)=1+d(c,y). Consequently the two even-distance sets at x and c together cover all of V∖S, the vertices in S at even distance from c, and x. The three contributions are disjoint. Write e(S,c) for the size of the second. Then

    n − |S| + e(S,c) + 1 ≤ 2k+2.                         (1)

It follows that |S|≥2. Some vertex of S thus has degree at least k. Every vertex of S has degree at most |S|, so |S|≥k. If e(S,c)=0, every vertex of S touches c. Indeed, if a nonneighbor of c belongs to S, take a path from it to c and consider its first edge leaving the set of nonneighbors of c in S. The initial vertex of that edge lies at distance exactly two from c.

If S,T,U are three disjoint sides at the same gate, (1) for S gives e(S,c)=0 since |T|,|U|≥k and c lies outside all three. Cyclically all three sides consist entirely of contacts. Every vertex of T∪U lies at distance two from a contact in S. Their number is at least 2k and they are all distinct from that contact. This violates the hypothesis, since k>0. In particular a cut vertex has exactly two components after deletion.

## Distinct cut vertices cannot occur

Take two distinct cuts c,d. Let A be a component of G−c avoiding d and let B be a component of G−d avoiding c. The side distance equalities give A∩B=∅. Indeed a common x would satisfy both d(x,d)=d(x,c)+d(c,d) and d(x,c)=d(x,d)+d(c,d).

Put Z=V∖(A∪B), so c,d belong to Z. If u∈Z∖{c,d} has degree ≥k, its neighborhood is contained in Z∖{u}, hence |Z|≥k+1. In (1) at A the exterior is B∪Z, with |B|≥k. This forces |Z|=k+1, |B|=k, and e(A,c)=0. The same argument at B gives |A|=k and e(B,d)=0. Thus all of A and B touch their respective gates. The high vertex u is adjacent to all other vertices of Z, so every vertex in A∪B is at distance two from it. This contradicts the cap since |A∪B|=2k. Hence Z∖{c,d} has at most one vertex, since every vertex there is low.

An edge whose deletion disconnects the graph has endpoint even-set sizes summing to n. Its endpoints have distances of opposite parity to each vertex, since every path across a bridge uses it. Therefore the inequality n≥2k+3 forbids bridges. Also there is no degree-one vertex, since a singleton leaf would be a side at its neighbor in violation of |S|≥2.

If Z={c,d}, the only possible edge between A∪{c} and B∪{d} is cd. Connectedness makes it a bridge, a contradiction. Otherwise Z={c,d,u}; the extra vertex u must be adjacent to both c and d because it has degree at least two. If cd were absent, cu would be a bridge separating A∪{c} from the remaining vertices. Thus cd is present. For each vertex in A∪B∪{c,d}, its distances to c and d differ by one, with (1)'s gate-distance identity again giving this on A and B. Therefore |A|+|B|+2 ≤ distEven(c)+distEven(d) ≤ 2k+2. Both sides have size exactly k. Since u is low, every vertex of A and B has degree at least k. Each such vertex has at most k candidate neighbors, namely its own side excluding itself together with its gate. Thus all vertices touch their respective gates. Again u has 2k vertices at distance two, a contradiction.

It follows that G has at most one cut vertex. In the non-2-connected case, write c for the unique cut and A,B for the two components. The graph induced on A∪{c} is connected. Removing c leaves connected A. If another vertex x disconnects A∪{c}, any component avoiding c after deleting x is also separated in G−x, contradicting uniqueness. Thus both augmented sides are 2-connected, and each side has size between k and 2k by (1) for itself and its opposite. To conclude traceability it now suffices to give both augmented sides paths spanning the side and ending at c. Easwar and Johari prove the requisite rooted statement as Lemma 5.10, by appending a marker adjacent only to c. Their Theorem 5.11 reaches this same structure via the block tree. The no-branching result is the portion addressed by the accompanying Lean file.
