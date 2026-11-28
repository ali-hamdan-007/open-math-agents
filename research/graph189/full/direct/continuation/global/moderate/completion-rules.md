# Certificates for partial graph completions

Suppose the fixed lower and upper graphs have the same finite vertex set as G and satisfy L≤G≤U. The exceptional vertex is z. The ambient path target counts n−h−1 vertices. The deletion target counts p+1 vertices, where p is the order of the chosen longest path in G−z. The theorem checker_path_bounds supplies the two exclusions when every ambient path omits at least h+2 vertices and every deletion path has at most p vertices.

Graph189Completion.Rejection.sound proves that a completed decision tree excludes every admissible G in its interval. Admissibility includes the two upper bounds on path lengths, the floor on each degree, connectivity after each one-vertex deletion, and the positive even-distance cap. The program’s degree floor is k away from z and 2 at z.

| Certificate rule | Witness | Deduction |
|---|---|---|
| path | A distinct-vertex list with consecutive edges in L, in the full graph or after deletion | The same path exists in G |
| degree | The degree in U is below the required degree | G has too few neighbors |
| cut | A nonempty proper subset of the surviving vertices is closed under the U-edges after one deletion | The deletion of G is disconnected |
| even | More than k distinct targets are two lower edges away, different from the root, and nonadjacent in U | Each has distance exactly two in G |
| forbid | Adding an optional edge to L produces a forbidden path | G omits the edge, so the child removes it from U |
| force | A possible edge is incident to a vertex whose degree in U equals its degree floor | The actual and upper neighborhoods there agree, so the child adds the edge to L |
| split | A rejection in each of the two child intervals | Every actual graph belongs to one of the children |

Graph189Completion.lean contains the graph lemmas and vertex-list path certificates. Graph189CompletionCertificate.lean defines admissibility, the seven rules and their joint soundness proof. Graph189CompletionRows.lean translates finite neighborhood rows, binary masks, cut partitions and explicit distance-two witness pairs to these rules. In the mask convention, bit j of row i records adjacency from i to j. A row representation is valid when the masks are symmetric and loopless.

Graph189CompletionIso.lean transports the path, deletion, degree and even-distance bounds across a graph isomorphism. The excludes_relabel theorem applies a rejection on Fin n to the original graph through its chosen vertex enumeration.

The soundness theorem applies to every finite graph. To certify a family of candidate patterns, a generator must also exhibit a rejection for each pattern and establish that the candidate generation covers the intended search space.
