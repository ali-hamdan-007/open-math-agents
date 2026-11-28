# Endpoints of a maximum-size path in a two-path cover

Suppose a connected graph G has a spanning cover by two nonempty vertex-disjoint paths and has no Hamiltonian path. Choose such a cover P,Q to maximize the order of its larger path P. Write X=V(P), Y=V(Q), h=|Y|, and let x,z be the endpoints of any Hamiltonian path on G[X].

Every endpoint of any Hamiltonian path on X has no neighbor in Y. Otherwise, append a nonempty end segment of Q starting from such a neighbor, keeping the remaining end segment as the second path. This either increases the larger path or gives a spanning path. Also x and z are nonadjacent. Otherwise the Hamiltonian cycle on X can be opened at any vertex having an outside neighbor, which exists by connectivity. The case |X|≤2 is immediate directly from connectivity and maximality.

Assume that both x can reach Y in G−N[z] and z can reach Y in G−N[x]. Since Y is connected and has no edges to either endpoint, each of these paths can extend to every vertex y of Y in the corresponding graph. If one x,z-path avoids N[y], then x,z,y is an asteroidal triple. Consequently, in an AT-free graph every x,z-path dominates Y. In particular, if x and z have common neighbors, every common neighbor is complete to Y. Each x-a-z path with common neighbor a proves this for a.

Suppose now h≥2, the graph is AT-free, every vertex has at most k vertices at distance exactly two, both accessibility conditions hold, and K=N(x)∩N(z) is nonempty. Then

    h+|K| ≤ k−1.

To prove this, mark the vertices of K along a fixed spanning x,z-path of X. Between any two marks there are at least h internal vertices, and there are at least h vertices in each tail beyond the outer marks. If the number between two marks is less than h, replace the intervening vertices by Q, placing those intervening vertices in the second path. A zero-length intervening segment gives a Hamiltonian path. The same replacement argument works for a tail. These replacements are possible since each mark is complete to Y.

The immediate predecessor and successor of every mark on the path are endpoints of paths spanning X. Rotating from x around the mark exposes its predecessor, while rotating from z exposes its successor. They all have no neighbor in Y, so none is a mark. The spacing and h≥2 make all 2|K| of these vertices distinct from each other and from x,z. Each is adjacent to a mark, and since it is outside K it misses at least one of x,z. Charge it to the distance-two set of an endpoint it misses. Each endpoint already has the opposite endpoint and all h vertices of Y at distance two via any mark. Therefore 2|K|≤2(k−h−1), giving the desired inequality.

Thus whenever h≥k−1 (and h≥2), either the endpoints have distance at least three or deletion of one endpoint's closed neighborhood separates the other endpoint from Y. If the endpoints are both of degree at least k, the common-neighbor bound also gives |X|≥2k+2−|K|≥k+h+3 in the accessible distance-two case. These statements are necessary conditions on two-path covers and do not by themselves give traceability.
