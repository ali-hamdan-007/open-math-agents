# Moderate orders, degrees three through six

I checked the independent implementation in moderate-completion-independent.cpp against the paper reduction and the coordinator’s moderate_exterior_search.py and moderate_completion.py. In this calculation 2k+3≤n≤3k+2, G is 2-connected, z is chosen so the other vertices all have degree at least k, H=G−z is connected, and P is a longest H-path. It uses the earlier result that a G-path missing at most ceil(k/2)+1 vertices implies traceability. This last implication combines the unrestricted exterior-size result and the almost-spanning theorem for the possible singleton low. The earlier exterior-size proofs cover k=3,4 directly and do not use the present completion calculation.

Writing p=|P|, b=|H−P|, h=ceil(k/2), the missing-vertex result gives b≥h+1. The degree floor k−1 in H gives p≥2k−1 by comparing the two endpoint neighbor sets along a nonspanning longest path. A coincidence in the opposite shifted sets would close a cycle on P, which can be extended since H is connected. Thus b≤k+2 and p≤3k+1−b. Every nonisolated exterior vertex has exterior degree q≥h−1 by the checked two-vertex contact count. Each isolated exterior vertex is high in G, forces the edge to z, and uses every even slot on P. Two such vertices would see each other at distance two through z. This proves the one-isolate filter even if other exterior components contain edges.

The search enumerates each simple exterior graph up to relabeling. Given a vertex v, the longest exterior path from v bounds both tails at any P-contact. A longest exterior path on l vertices from v to w also forces distinct P-contacts to be at index distance at least l+1. Equal contact positions are allowed. Degree in H requires at least k−1−q contacts. For q>0 the neighbor contact inequality gives at most q+1. An isolate has exactly k−1. Specifically, along an exterior edge xy one has a(x)+deg_H(y)≤k+q(x). These two orientations are the only pairwise degree restrictions. A component must touch P by connectivity.

All edges touching an exterior vertex within H are then fixed. If its degree in H is k−1, its edge to z is forced. An initial two-step witness is counted only when every possible completion keeps the endpoints nonadjacent. The remaining optional edges are precisely the unassigned path chords and the still unassigned edges incident with z. A path in a lower graph survives all completions. Thus an optional edge whose addition creates a too-long path can be removed from the upper graph. Conversely every optional neighbor of a vertex is compulsory when its upper degree equals the required minimum, which is k away from z and 2 at z. A cut vertex or a degree deficit in the upper graph prevents the original 2-connected graph. A lower-graph two-step walk with a missing upper-graph edge is a permanent distance-two witness. All of these tests exclusively exclude impossible completions. Propagation alone suffices.

The C++ replay uses independently written unlabeled-graph enumeration, attachment placement, longest path checks and propagation. Canonical labels order vertices by local degree and codegree signatures, then minimize the adjacency encoding over unresolved classes. Interchangeable twins need no permutations. Vertex extension and the known unlabeled counts through order eight give 1, 2, 4, 11, 34, 156, 1044 and 12346. The C++ replayer contains path, cut and relabeling controls. To run, compile with a C++17 compiler and pass 6 as its sole argument.

| k | Exact partial patterns | Mandatory path | Further propagation | Survivors |
|---|---:|---:|---:|---:|
| 3 | 9 | 8 | 1 | 0 |
| 4 | 30 | 7 | 23 | 0 |
| 5 | 51 | 7 | 44 | 0 |
| 6 | 98 | 4 | 94 | 0 |

No branch over optional edges was necessary. The search and replay are executable evidence conditioned on the graph reductions. They do not provide a Lean kernel certificate.
