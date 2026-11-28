# Any edge outside all triangles forces bounded order under Graph 189

**Theorem.** Let G be finite and 2-connected, with k≥1. Suppose every vertex sees at most k others at positive even distance. If an edge xy belongs to no triangle and d(x)≥k, then |V(G)|≤3k+2. No lower degree assumption on y or on the other vertices is needed.

Write W=N[x]∪N[y], B=N(W)∖W for its outer boundary and Z=V(G)∖(W∪B). The disjoint sets N(x),N(y) together equal W, so |W|=d(x)+d(y). Within W, the d(y)−1 neighbors of y distinct from x have distance two from x, and the d(x)−1 neighbors of x distinct from y have distance two from y. Thus x has at most k−d(y)+1 positive-even places outside W, and y has at most k−d(x)+1≤1. Every boundary vertex has distance two from at least one of x,y. Consequently

    |B| ≤ 2k+2−d(x)−d(y),     |W|+|B| ≤ 2k+2.

If a vertex outside W has distance two from y, it is the only such vertex, b, and exhausts y's positive-even places outside W. This b belongs to B. Since W lies within radius two of y, y has no fourth layer, hence all vertices in Z, if any, are at distance three. The penultimate vertex of a shortest path from y to z∈Z cannot lie in W, and therefore equals b. A neighbor of b in W sees all of Z at distance two via b, giving |Z|≤k.

Otherwise every vertex z of Z is at distance at least four from y. A shorter path to z would need a level-two vertex outside W, since z has no neighbor in W. The fourth layer has size at most one, by y's even-distance budget. If the fifth layer existed, the fourth layer would be a one-vertex cut, contrary to 2-connectivity. Therefore Z lies entirely in the fourth layer and |Z|≤1≤k. This proves the order bound in both cases.

**Consequence for Graph 189.** The previously independently reviewed bounded-order theorem gives a Hamiltonian path for every qualifying graph of order at most 3k+2. Easwar–Johari's cut-vertex theorem covers connected graphs that are not 2-connected. Because at most one vertex has degree below k, each edge has an endpoint of degree at least k. It follows that every edge of any counterexample lies in a triangle. Equivalently, every nonempty neighborhood induces a subgraph with minimum degree at least one. Each vertex v therefore belongs to at least ceil(d(v)/2) triangles. The structural order estimate is independent of the bounded-order and cut-vertex theorems; those implications are needed only for the traceability conclusion.
