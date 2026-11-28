# An order bound from a root's second layer and its application to exterior contact matchings

Let G be any finite connected simple graph with at most k other vertices at positive even distance from each vertex. Write f(p)=p(k+1−p). For any root c and any inclusion-minimal set T of neighbors of c whose neighborhoods cover its distance-two layer, set p=|T|. Then

    n ≤ 1 + d(c) + k + f(p).

For every v at odd distance at least three from c, take the second vertex after c on a shortest path to v. This vertex belongs to the second layer and has a neighbor a∈T. The path from a through it to v and the triangle inequality give d(a,v)=d(c,v)−1, which is positive and even. Each j∈T has a distinct private second-layer witness b_j adjacent only to j among T. For each a∈T and j≠a in T, there is a distance-two witness in the first two layers, namely j if a and j are nonadjacent, or b_j via j if they are adjacent. Each a reserves p−1 distinct quota places for these witnesses and can cover at most k+1−p odd vertices from the more distant layers. Summing over T and adding the root, its immediate neighbors and all its other positive even vertices proves the bound. The empty-cover case has no vertices beyond the first layer. This extends the third-layer argument in the earlier third-layer-and-global-order.md to all odd layers. It uses neither a degree assumption on c nor a diameter restriction.

## Exterior setting

In a hypothetical nontraceable Graph 189 graph, let P be a longest path and C a high-bearing, 2-connected exterior component with order m≤2q−1, where q is its least internal degree among high vertices. Assume the established exterior hypotheses m≥ceil(k/2)+2 and q≥ceil(k/2). Let j be the maximum size of a matching between C and P, with j≥2 here. Every pair of distinct C terminals has a spanning route, except possibly the two unique C-neighbors of a low C vertex of internal degree two. That pair still admits a route on m−1 vertices. The known matching count is n≥(j+2)m+j−1. It follows from this count and n≤1+2k+floor((k+1)²/4) that j<floor(k/2) at even and odd k: with t=floor(k/2), even k=2t and m≥t+2 give n≥t²+5t+3 at j=t, exceeding U=t²+5t+1, while odd k=2t+1 and m≥t+3 give at least t²+6t+5>U=t²+6t+4.

Fix a minimum cover of these bipartite contact edges, consisting of M⊆P and Y⊆C, and write u=|Y|, |M|=j−u. Any maximum j-matching touches each cover member exactly once and no matching edge joins two cover members. Thus its set of j labels on P contains every member of M. Write r=m−1+j−k. At least one high c∈C−Y is available since m−1>j. Let b be the number of members of C−{c} nonadjacent to c and z the number of M marks missed by c. Then

    d(c)=k+r−u−b−z,    b+z≤r−u.

A cover of the distance-two layer of c needs at most j+b actual neighbors of c. Use all neighbors in M, and allow one actual neighbor witnessing distance two to each missed member of M when needed. Add all neighbors in Y for the possible extra path contacts of these C vertices. Allow one covering witness for each of the b interior nonneighbors at rooted distance two. Indeed any other exterior-to-C second step from a C-neighbor outside Y ends in M, and any step starting with a mark neighboring c was already covered. There can be no edge between C and another exterior component. This covers the entire layer. Shrinking to an inclusion-minimal cover gives p≤j+b. Since j≤(k+1)/2, concavity gives f(p)≤f(j)+b(k+1−2j), including if j+b exceeds the vertex of this quadratic.

Let ε=0 when C is Hamilton-connected, and let ε=1 when only the near-spanning terminal conclusion is used. Each of the j+1 pieces of every path ordering on V(P) has at least L=m−ε unmarked vertices. These include both tails. Write σ for their total excess. A high attainable endpoint has at most L−1+σ neighbors outside the j matched marks: a neighbor in the first L places after any mark would rotate that mark onto an impermissibly short initial tail. Since c misses at most u+z of the matched marks and there are at least k+1 high attainable endpoints, k−L+1−σ≤u+z. Otherwise every such endpoint would share a matched mark with c and would lie at distance two from it. Thus n≥m+jL+j+k+1−u−z. Subtracting the local cover upper bound using the previous display gives a difference, lower minus upper, of at least

    1 + j(r−ε) + b(2j−k).

In particular, if 3j≥k then this is at least 1+j(r−ε−b)≥1+j(u−ε). Accordingly a mixed cover or a Hamilton-connected C is impossible at 3j≥k.

## The tight exterior sizes

The pure full-contact case r=0 is impossible for every eligible j, even below k/3. Its cover must consist of j marks. Every high c of C is internally universal, touches every mark and has degree k. Its entire second layer is covered by the j marks. The endpoint count with L=m gives n≥(j+2)m+2j=2k+2+f(j), whereas the local cover gives at most 2k+1+f(j).

The next case r=1 is likewise impossible for every eligible j. If there is a mixed cover, it uses a single C vertex u. A high c∈C−u is internally universal, touches all j−1 real marks and has degree k. The j−1 marks together with u cover its second layer, and c misses just one of the j matched labels. For a pure cover, if a high c misses a mark then it misses exactly one, and is internally universal of degree k. Its j−1 adjacent marks and a C contact of the remaining mark cover its whole second layer. If instead every high C vertex meets every mark, choose a high c adjacent to the possible low C vertex, which is feasible by connectedness; without a low C vertex choose any high c. Every C nonneighbor of c is high and shares the marks with c, so the marks alone cover its second layer; d(c)≤k+1. In the first two cases c misses one matched label and d(c)=k. In the final case it misses none and d(c)≤k+1. Write e for this number of missed labels. The endpoint count even with L=m−1 gives n≥m+j(m−1)+j+k+1−e=2k+3+f(j)−e. In all cases the root upper bound is at most 2k+2+f(j)−e. This contradiction needs no assumption on the degree of a possible low member.

Finally suppose 3j≥k, the cover is pure, and there is a terminal obstruction. Its low C vertex w has only two internal neighbors and at most j marks, so d(w)≤j+2. Its own trivial second-layer cover has size at most j+2. The local order bound and quadratic tangent then give n≤f(j)+3k−3j+5. On the other hand the usual near-spanning matching count gives n≥f(j)+2k−j+1+(j+2)r. For r≥2 the difference is at least 4j−k>0. The cases r=0,1 were excluded directly. Thus, in full generality,

    every near-Hamilton-connected exterior as above satisfies 3j<k and m≥k−j+3.

This signature applies to arbitrary longest paths meeting the stated exterior hypotheses. No computational case enumeration is used. It is compatible with arbitrarily low unique vertices and with additional components outside the selected path.
