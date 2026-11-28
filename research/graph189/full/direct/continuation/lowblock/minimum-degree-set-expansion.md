# Simultaneous deletion of locally minimum-degree vertices

Let G be connected and suppose every vertex has at most k other vertices at positive even distance. Let S be a vertex set, H=G−S, and assume at most one surviving vertex has fewer than k neighbors in H. Suppose each v∈S has degree at most the degree of every neighbor of v in G. Then all distances among survivors are unchanged by deleting S.

For two survivor vertices choose a shortest G-path between them using as few vertices of S as possible. If it enters S, take a maximal consecutive interval of its S vertices. Its two bordering survivors are distinct, so at least one of them, x, has d_H(x)≥k. Orient that segment away from x, with first deleted point v and following point y. The vertices x,y are nonadjacent by shortestness. Their neighborhoods lie in B₂(v) outside x and y, a set of order at most d(v)+k−1, giving

    |N(x)∩N(y)|≥d(x)+d(y)−d(v)−k+1≥d(x)−k+1>|N(x)∩S|.

One can therefore replace v by a common neighbor outside S. The resulting equal-length walk cannot repeat a vertex, since the original path was shortest. It is a shortest path with fewer entries in S, a contradiction. This proves isometry and hence connectedness of H when it has survivors.

In particular, let G be a minimum-order Graph 189 counterexample, k its second-smallest degree, h=ceil(k/2). Any nonempty set S of at most h+1 locally minimum-degree vertices has at least two distinct vertices x outside S satisfying

    |N(x)∩S|>d(x)−k.

Indeed otherwise the preceding lemma makes H an isometric connected qualifying graph. It has at least two surviving vertices by the general order lower bound; by minimum order it is traceable. A spanning path in H misses at most h+1 vertices of G, impossible by the global almost-spanning/exterior-size theorem. This necessary degree expansion is independent of saturation.

There is an extension covering the whole low-degree set D={v:d(v)≤k}. If the minimum degree is tied, every member of D is locally minimum. If the unique low vertex is z, require z∈S and allow any additional members of D in S. The earlier verified isometric deletion of z lets us take the original shortest path above avoiding z, still minimizing its number of entries in S among such paths. For its subsequent deletion point v the following y is not z and d(y)≥k=d(v); the alternative neighbor outside S also avoids z. Thus the same two-vertex expansion holds for every such S⊆D of size at most h+1. One may also include other local minima with respect to the original degrees of their neighbors other than z.

For example, if the tied degree-k set has order at most h+1, some two distinct higher-degree vertices x receive at least d(x)−k+1 neighbors from that set. The same holds for the entire set of degrees at most k in a unique-low counterexample if its order is within that bound.
