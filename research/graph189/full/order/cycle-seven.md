# The auxiliary order bounds fail already in diameter three

Let k be the second-smallest degree of a finite connected graph, counting vertices with multiplicity. The Graph 189 hypothesis bounds, for each vertex, the number of other vertices at positive even distance by k. Both additional proposals n≤3k+1 and n≤3k+2 fail. In fact n−3k can be arbitrarily large, even for Hamiltonian graphs of diameter three.

Take a cycle on seven classes indexed modulo 7. Replace class i with a clique of size sᵢ, and join every vertex in each pair of consecutive classes. For different classes the distance of two vertices is precisely the distance of their indices on the seven-cycle: every path in the graph projects to a walk of no greater length on that cycle, and a shortest index path lifts. Other vertices of the same class are adjacent. Accordingly the degree in class i is sᵢ₋₁+sᵢ+sᵢ₊₁−1, while the positive even-distance count is sᵢ₋₂+sᵢ₊₂.

For a concrete example, the following table gives the complete construction and its verification.

| Class | Size | Degree | Vertices at positive even distance |
|---:|---:|---:|---:|
| 0 | 3 | 8 | 8 |
| 1 | 3 | 9 | 8 |
| 2 | 4 | 11 | 8 |
| 3 | 5 | 13 | 7 |
| 4 | 5 | 13 | 7 |
| 5 | 4 | 11 | 8 |
| 6 | 3 | 9 | 8 |

Three vertices have minimum degree eight, so the second-smallest degree is k=8. The maximum positive even-distance count equals eight. The order 27 exceeds both 3k+1=25 and 3k+2=26. Visiting all vertices of each clique in turn around the cycle gives a Hamiltonian cycle. This establishes 2-connectivity as well. The example refutes the proposed order bounds and satisfies the Hamilton-path conclusion of Graph 189.

For any integer t≥1, choose class sizes (1,1,1,1,1,1,1)+t(2,2,3,4,4,3,2). The class degrees are 2+t(6,7,9,11,11,9,7) coordinatewise, and the even-distance counts are 2+t(6,6,6,5,5,6,6). Hence k=6t+2, n=20t+7=(10k+1)/3, and n−3k=2t+1. All these graphs are Hamiltonian. No uniform additive constant can yield an order bound of the form n≤3k+C.

The companion Python verifier constructs the indicated graph explicitly, obtains all degrees and even-distance counts by breadth-first search, checks connectivity after every one-vertex deletion, and verifies the supplied Hamiltonian cycle. Run “python order_counterexample.py” for the 27-vertex graph, or pass an integer t for another member.
