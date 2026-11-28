# Whole-parameter results at second-smallest degree four and five

For a two-connected qualifying graph with minimum degree at least three, n≤14 when its second-smallest degree k is four, and n≤17 when k is five. Thus the previous n≤3k+2 and minimum-degree-at-most-two and cut-vertex results establish traceability for the full conjecture at k=4 and k=5. The new order bounds are finite-computation results. The separate handwritten argument k3-order.md covers k=3.

Use the previously proved diameter bound ≤4 in this range: all high pairs are at distance at most four, all graphs have diameter at most five, and the available diameter-five result requires minimum degree greater than five for a two-connected graph here. Write z for a minimum-degree vertex, a=deg(z)∈{3,…,k}, and A,B,C,D for its successive distance layers. Then b+d≤k. The b=0 case has order a+1. If c=0 then n≤1+a+k≤3k+2.

## Exterior counting profiles

Fix a graph on the a labeled anchors A. Each B-column has nonempty anchor support. For each c∈C choose one incident B column and call the number assigned to column j its load f_j. For anchor i let R_i be its set of B columns and d_i its number of neighbors among A. Then

    1+d_i+|R_i|≥k,
    Σ_{j∈R_i} f_j ≤ k−(a−1−d_i)−|(⋃_{l adjacent to i in A}R_l)∖R_i|.

The witnesses on the right are the missed anchors via z and the missed columns reached through another anchor. They are disjoint from the assigned C vertices. All loads lie in 0,…,k because every B column meets an anchor. A high-order candidate has c=Σf_j and must admit a fourth-layer size d between max(0,3k+3−1−a−b−c) and k−b. The code enumerates every anchor graph, support multiset, load vector and such d. Permuting A, permuting columns with their loads, and ordering C by its assigned column loses no completion. Since additional B–C edges remain optional, the choice of a single assignee per C never restricts the final graph.

## Forced and possible edges

For each candidate construct L⊆G⊆U. Initially U allows all edges within or between consecutive permitted layers, except that root/anchor edges, the anchor graph, and A–B incidences are exact. L consists of the required edges there and one B–C edge for each allocation. Rejection rules are necessary for every completion:

* Each nonroot vertex must have at least k possible neighbors, with a possible neighbors at the root.
* A vertex guaranteed to be at distance two from x by an L two-edge walk and a missing U edge costs one even-distance witness.
* Every vertex outside the U-ball of radius three about x must be at distance four in G. If U cannot reach it in four steps, the branch is impossible. Otherwise include it as another even-distance witness.
* Reject when the union of these definite even sets exceeds k at any vertex.

When a vertex's possible degree equals its lower bound, force all possible incident edges. For an undetermined edge, test each assumption with the rejection rules. If one assumption is impossible set the opposite value. When propagation stops, branch into the two disjoint possibilities for one undetermined edge. At a fixed graph that has survived all rejections, count the graph. The count is zero. The verifier does not need a Hamilton path algorithm, two-connectivity tests or second-degree tie checks: removing those extra constraints only enlarges the searched set.

## Replay

Compile `layer_order.cpp` with a C++17 compiler, for example `c++ -std=c++17 -O3 layer_order.cpp -o layer_order`. Run `./layer_order k a` for the five rows here. The logged classes are canonical incidence profiles together with their possible d values. Values listed from b=1 upwards.

| k | a | Maximal scalar c by b | Classes searched by b | DFS calls by b | Completions |
|---|---|---|---|---|---|
| 4 | 3 | 4,6,6,6 | 0,0,0,0 | 0,0,0,0 | 0 |
| 4 | 4 | 4,6,6,6 | 0,5,18,53 | 0,17,32,165 | 0 |
| 5 | 3 | none,5,8,9,9 | 0,0,0,1,2 | 0,0,0,1,4 | 0 |
| 5 | 4 | 5,8,9,9,9 | 0,2,9,43,124 | 0,182,17,55,158 | 0 |
| 5 | 5 | 5,8,9,9,9 | 0,35,426,2339,8406 | 0,243,1768,4425,34158 | 0 |

The independent k=4 tied-degree reimplementation is in `../review/k4-independent.py` with a separate log; it found the same 76 canonical allocations and zero graphs in 1,535 search calls using different branching and propagation. Exact k-specific logs for the main implementation are `layer-k4-a3.log`, `layer-k4-a4.log`, `layer-k5-a3.log`, `layer-k5-a4.log`, and `layer-k5-a5.log`. These are local computations, not Lean proofs.
