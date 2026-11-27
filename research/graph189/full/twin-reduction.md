# True-twin reductions for Graph Conjecture 189

For a connected simple graph G of order at least two, let e_G(x) count the vertices at even distance from x, including x, and let s(G) be the second entry in the nondecreasing degree sequence, with multiplicity. Call the graph admissible when every e_G(x) is at most s(G)+1.

## Deleting one twin

Suppose G has at least three vertices and u,v are adjacent true twins, meaning their closed neighborhoods are equal. Write H for G with u deleted and s=s(G). Distances between remaining vertices are unchanged. A shortest path whose internal vertices include u can use v in its place: if the path already contains v then it shortcuts past u by the twin adjacency. Equivalently, fold u onto v along a shortest path, discard repeated consecutive vertices, and shorten the resulting walk. The reverse inequality holds since H is induced. Therefore

$$
e_H(x)=e_G(x)-\mathbf{1}_{\{d_G(x,u)\text{ even}\}}
$$

for every remaining x. Each remaining degree drops by at most one. The second degree of the subsequence obtained by deleting u from the original degree list is at least s, so s(H) is at least s−1.

If G is admissible, H is admissible whenever s(H) is at least s. In the only other case, s(H)=s−1, H is admissible exactly when every remaining x with e_G(x)=s+1 is at even distance from u. A spanning path of H always lifts: insert u immediately after v on the path, using the identical outside neighbors. If v is the last endpoint, append u.

It follows that, in a minimum-order counterexample, deleting any member of any nontrivial true-twin class must decrease the second degree by exactly one and some remaining saturated vertex must have odd distance to the deleted vertex. This is a restriction on hypothetical counterexamples, not an existence assertion.

## Uniform clique expansion

Let B be a connected simple graph of order at least two. Replace each vertex by a clique of the same size t≥2 and each edge by all edges between the two corresponding cliques, obtaining G. At any vertex over b the degree is t(d_B(b)+1)−1. Each fiber realizes this degree at least twice, so s(G)=t(δ(B)+1)−1. Distances between distinct fibers are base distances and the other vertices of the same clique are at distance one. Thus e_G(x)=1+t(e_B(b)−1). Integrality makes admissibility of G equivalent to e_B(b)≤δ(B)+1 for all b, which implies admissibility of B.

If B has a spanning path, replacing each of its vertices by any ordering of its clique gives a spanning path of G. Thus a minimum-order counterexample cannot be such a uniform expansion. In particular, if nontrivial true-twin classes and singleton classes partition a graph and the greatest common divisor of all class sizes is greater than one, grouping each class into equal-sized blocks expresses it as a uniform expansion of a smaller graph. A complete graph, or a one-block case, is already traceable.

These are paper deductions. They do not transfer traceability in the reverse direction or prove that a minimal counterexample is twin-free.
