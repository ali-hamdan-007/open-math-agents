# A connected high-order k=6 residual has at least four second-layer vertices

Assume a unique degree-five root z, all other degrees at least six, positive even-distance cap six, diameter at most four, and n>20. The preceding defect-four reduction and three-exception argument leave |L₂|=3 only if |L₄|=3. The latter possibility is excluded by the finite census below. Thus every nontraceable graph in this regime has |L₂|≥4 and |L₄|≤2.

Write A=L₁, P=L₂, R=L₃, F=L₄. In the case to exclude the four layer sizes are 5,3,h,3 with h=n−12≥9. The C++17 source k6-connected-three-port-probe.cpp has SHA-256 e647296cded42ae2ddd4a464a96486a83909b8b6bc48c7a4c9be5245ee43145a. Compile with g++ -O3 -std=c++17 and run without arguments. The standard output is k6-connected-three-port.log.

For a port p let S_p denote its contacts in R. Choose the port subsets I(a) for the five anchors, sorted and then made canonical under the six port permutations. Each subset is nonempty because only five potential neighbors exist for an anchor outside P. No anchor touches every port, since h>6, and the subsets cover P. Try all 1,024 anchor graphs and all eight port graphs. An anchor must have at least five combined neighbors among A and P because its only other possible neighbor is z.

An anchor's touched supports have union bounded by six less the number of its nonneighbor anchors (all at distance two via z) and the number of its nonneighbor ports already reached in two shell edges. There is at least one such witness: if it meets all other anchors, any missed port is reached through one. Hence each such union has size at most five. Individual port supports must also be large enough to reach degree six after counting their anchor and port neighbors.

Each port sees z at distance two. From the other five even slots subtract every nonneighbor anchor or other port reachable in two shell edges. The resulting nonnegative number b_p bounds further even witnesses. In particular the supports of the ordinary neighbors of p add at most b_p vertices outside S_p. Propagate upper bounds on unions to subsets and by addition across disjoint pieces. This leaves no shell with h>10. The elementary bound h≤15 also follows from the three supports of size at most five.

For each allowed h, enumerate sorted nonempty port masks M_i of the h vertices of R, enforcing the support and union bounds. For each fourth-layer vertex f enumerate J_f, its set of ports at distance two; these masks are sorted within F. Every R-neighbor i of f must have M_i⊆J_f. As d(f)≥6 and at most two neighbors lie in F, an eligible J_f must permit at least four such i. If an anchor a has I(a) disjoint from J_f, then f is at distance four from a: it cannot be reached in three steps without a path a,p,i,f, and the diameter is at most four. Charge that additional witness at a.

At each port charge any new distance-two port pairs witnessed by an overlap in R, and every f with p∈J_f. For every i∈R its distance-two port mask Z_i is disjoint from M_i and must contain any port that misses i but touches a member of M_i. If M_i={p} and |S_p| plus the number of f with p∈J_f is below six, then i needs a core neighbor outside S_p and hence Z_i must be nonempty. Enumerate the remaining Z_i, sorting within each common M_i class and respecting the remaining even slots at all ports.

A feasible core edge i,j requires M_i⊆M_j∪Z_j and M_j⊆M_i∪Z_i. Count all such edges as available, along with all f contacts permitted by M_i⊆J_f and all edges inside F. Reject insufficient potential degrees at R or F. Finally, for each f, the union of M_i over its possible R-contacts must contain J_f: a two-edge path from f to a port can go only through R. The reverse inclusion already holds by the definition of possible contacts.

| h | Shells | R masks | With F masks | Further distance checks | With R even masks | Degree checks | Realizable F masks |
|---|---:|---:|---:|---:|---:|---:|---:|
| 9 | 302 | 312 | 15645 | 9 | 8 | 7 | 0 |
| 10 | 32 | 14 | 784 | 0 | 0 | 0 | 0 |
| 11–15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Every actual graph has one of the sorted representations and meets each of these necessary tests. Thus there is no qualifying graph in this last three-port case.
