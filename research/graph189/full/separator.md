# A weighted matching obstruction to separator counterexamples for Graph 189

Let G be a connected simple graph, let σ be its second-smallest degree, and assume each vertex has at most σ other vertices at even distance. A spanning path can meet at most |S|+1 components of G−S, so c(G−S)>|S|+1 certifies nontraceability.

## A separator inequality for dense attachments

Let S be any nonempty vertex set. For each component C_i of G−S, let T_i be the set of vertices of S adjacent to some vertex of C_i, and let t_i=|T_i|. Connectivity gives t_i>0. Define α_i as the minimum, over a∈T_i, of the number of neighbors of a in C_i.

Suppose each component C_i has a vertex x_i adjacent to all of T_i, with degree at most t_i α_i. Then c(G−S)≤|S|+1.

Consider the incidence bipartite graph between the components and the vertices of S, with edges i–a when a∈T_i. Take a maximum matching that maximizes the sum of α_i over its matched components. If i is unmatched, every a∈T_i is matched, since otherwise the edge i–a could increase the matching size. If its mate is j_a, then α_{j_a}≥α_i, since otherwise replacing j_a–a by i–a increases the weight without changing the matching size. Distinct anchors a have distinct matched components.

If c(G−S)>|S|+1, there are two different unmatched components i and j. Choose i with degree(x_i)≥σ. This is possible because at most one vertex of G has degree below σ. Each of the t_i matched components j_a contributes at least α_i vertices at distance exactly two from x_i through a. Different components of G−S have no direct edges. The witnesses therefore give at least t_i α_i≥σ distinct positive even distances from x_i.

There is one more witness, as follows.

- If T_i and T_j meet, a neighbor of a common anchor in C_j is at distance two from x_i.
- If the profiles are disjoint and some a∈T_i is adjacent to b∈T_j, then b itself is at distance two from x_i.
- If the profiles are disjoint and there is no such edge, then the graph distance from x_i to x_j is at least four. A walk of length two would need a common anchor. A walk of length three would require a common anchor or an edge from T_i to T_j, by inspecting its two interior vertices. A shortest path supplies a vertex at distance exactly four from x_i.

None of these additional witnesses belongs to the previous distance-two collection. This contradicts the cap.

## Infinite families covered

1. **Homogeneous attachment.** Every vertex of C_i sees the same nonempty T_i. Set w_i=|C_i|. Then α_i=w_i and degree(x_i)≤w_i−1+t_i≤t_i w_i. The internal graphs of S and the C_i can be arbitrary.
2. **Attachment missing at most one vertex.** Each C_i has size w_i≥3, touches at least two anchors, each touched anchor sees at least w_i−1 vertices of C_i, and some x_i touches all its anchors. Then α_i≥w_i−1 and t_i(w_i−1)≥w_i−1+t_i. Internal graphs are again arbitrary.

This rules out the specific separator obstruction for these families. Easwar and Johari's [preprint](https://arxiv.org/abs/2609.11719) proves full traceability under hypotheses involving order, diameter and vertex connectivity. The incidence-matching argument targets arbitrary separators of a restricted attachment type. It does not rely on their traceability results.

## A separate incidence bound for clique separators

Suppose S is a clique of size s≥2, every outside vertex touches S, and every outside vertex misses at least k≥1 vertices of S. Write n₀=|V(G)−S|. Each anchor a in S has every outside nonneighbor at distance two: choose an anchor adjacent to that outside vertex, and use the separator clique edge. Summing each anchor's cap gives k n₀≤sσ.

Every component with a vertex of degree at least σ has size at least σ+1−s, by bounding its internal and separator degrees. At most one component can lack such a vertex, and that component must be a singleton. For a separator obstruction with at least s+2 components and σ≥s, it follows that n₀≥(s+1)(σ+1−s)+1. In particular, k=1 excludes every such obstruction for σ>s²−2. If every component has a vertex of degree at least σ, the sharper bound n₀≥(s+2)(σ+1−s) excludes σ>(s+2)(s−1)/2 for k=1. This argument allows fully heterogeneous attachment profiles.
