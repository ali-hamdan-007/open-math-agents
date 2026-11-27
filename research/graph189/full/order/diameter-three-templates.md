# Sharp order for diameter-three clique blow-ups with at most eight classes

Let H be a connected graph of diameter three on at most eight vertices. Replace its vertices by nonempty cliques and join two cliques completely exactly when their template vertices are adjacent. Let k≥2 be the second-smallest degree of the resulting graph G, and suppose every vertex of G has at most k other vertices at positive even distance. Then

    |V(G)| ≤ ⌊(10k+1)/3⌋.

For every k≥2, some 2-connected Hamiltonian example attains this bound. Thus this result determines the exact maximum order in the stated template class. The proof of the upper bound is computer-assisted. It places no upper bound on the clique sizes or on k.

## Verification by counting covers

Write wᵢ for the size of class i. Distances between different classes in G are the template distances; different vertices in the same class have distance one. For each class i, the sum of the weights in the template's positive even-distance set Eᵢ is therefore at most k. If h is a class containing a minimum-degree vertex of G, the sum over its closed neighborhood Bₕ is at most k+1.

If three of the sets Eᵢ cover all template vertices, then n≤3k. If there is a cover by Bₕ and two even-distance sets for every possible h, then n≤3k+1. Both bounds imply 3n≤10k+1 for k≥2.

For the remaining graphs, the verifier uses covers in which each vertex is covered at least three times. For every possible h it specifies nonnegative integer multiplicities for the even-distance sets and for Bₕ. Let T be their sum and b the multiplicity of Bₕ. Summing the neighborhood bounds gives 3n≤Tk+b. Each saved cover has T≤10 and 2T+b≤21. Hence (10−T)(k−2)+21−2T−b≥0, which proves Tk+b≤10k+1.

The complete results are as follows. The simple-cover columns are disjoint; a graph counted in the closed-ball column did not pass the three-even-sets test.

| Template vertices | Connected templates | Diameter three | Three even sets | Ball and two even sets | Used triple covers |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 0 | 0 | 0 | 0 |
| 3 | 2 | 0 | 0 | 0 | 0 |
| 4 | 6 | 1 | 0 | 1 | 0 |
| 5 | 21 | 5 | 1 | 4 | 0 |
| 6 | 112 | 43 | 13 | 30 | 0 |
| 7 | 853 | 387 | 223 | 163 | 1 |
| 8 | 11,117 | 5,797 | 4,392 | 1,401 | 4 |

The standalone program verify_small_template_bound.py uses only the Python standard library. Run it using ordinary Python (assertions enabled). It constructs all connected graphs by adding one vertex with a nonempty neighborhood to a smaller connected graph. Every finite connected graph has a vertex whose deletion leaves it connected, for example a leaf of a spanning tree, so this construction is exhaustive. To remove duplicates, it colors vertices by repeatedly refining their degree and the colors of their neighbors, then minimizes the adjacency encoding over all permutations within the final color classes. Equal encodings imply an explicit relabeling, and the color rules are invariant under isomorphism.

For each template the verifier computes the true distances by breadth-first search. It tests the two simple-cover conditions directly. The 39 short multiplicity vectors needed for the other five templates are embedded in the program. It confirms all coordinates, all coverage thresholds, each multiplicity budget, and the final total of 6,233 checked diameter-three templates with exact integer arithmetic. The separate affine-LP search used to discover the covers plays no role in verification.

## Sharpness

For k=2 and every k≥4, the seven-cycle clique blow-ups in sharp-seven-cycle.md attain the upper bound and have Hamiltonian cycles. For k=3, take a path of four cliques of respective sizes 2,2,3,3 and join consecutive cliques completely. Its ten vertices have class degrees 3,6,7,5 and positive even-distance counts 3,3,2,2. A Hamiltonian cycle traverses one vertex of each class from left to right, then travels back through every remaining vertex class by class. Consequently the required maximum at k=3 is also attained.

For completeness, at k=1 a leaf exists. Its neighbor has at most one further neighbor, since those vertices would all be at distance two from the leaf. Every vertex at distance three from the leaf has distance two from the leaf's neighbor, so at most one such vertex exists. Thus the only connected diameter-three example at k=1 is the four-vertex path. It achieves order four.
