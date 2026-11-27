# A split radius-two ball at a minimum-degree vertex

**Theorem.** Let G be a finite connected simple graph of minimum degree k≥2. Assume that every vertex has at most k other vertices at positive even distance. If some degree-k vertex z is a cut vertex of its own induced radius-two ball, then G has a Hamilton cycle.

The second-smallest degree σ of a graph can exceed its minimum only if the minimum is unique. The theorem applies directly to the δ=σ part of Conjecture 189 whenever the stated split ball exists. It permits unrestricted degrees above k and arbitrary diameter.

## The two sides of the ball

Write Nᵢ(x) for the vertices at distance i. Every component of B₂(z)−z contains a neighbor of z, since any length-two path from z reaches its endpoint through one of its neighbors. All the neighbors of such a neighbor lie in its component or are z. Minimum degree k therefore gives at least k vertices per component. On the other hand |B₂(z)−z|=k+|N₂(z)|≤2k. Hence there are exactly two components X and Y, each of size k, and |N₂(z)|=k. Its even-distance allowance is exhausted, so there is no vertex at distance four from z. A shortest path to any more distant vertex would pass through distance four, and hence every vertex lies within distance three of z.

Put A=X∩N(z), B=Y∩N(z), a=|A|, b=|B|, P=X∖A, Q=Y∖B and T=N₃(z). Then a,b≥1, a+b=k, |P|=b, |Q|=a. A vertex of A can have as neighbors only z and the other k−1 members of X, and must therefore see all of them. Similarly B is complete to Y. Every p∈P needs a neighbor in T because it has at most k−1 available neighbors elsewhere. Every q∈Q also needs a neighbor in T. Conversely, every t∈T sees P or Q along a length-three path from z.

Partition T into U,M,V according as a vertex sees only P, sees both P and Q, or sees only Q. Write u,m,v for their cardinalities. A vertex of A sees B and U∪M at distance two, whence u+m≤a. Likewise v+m≤b.

## The mixed vertices

Suppose m>0 and put F=G[P∪Q∪T]. For t∈M, all k members of A∪B are at distance two from t. The even-distance hypothesis gives N₂(t)=A∪B and eccentricity(t)≤3. Every component of F contains a remote vertex, since each p∈P and q∈Q has a remote neighbor. Two remotes in different F-components would be at distance at least four, since every joining path would reach A∪B∪{z} and each endpoint is at distance at least two from this set. Applying this to t proves F is connected. A vertex nonadjacent to t within F would then provide a vertex of F at distance exactly two from t along a shortest F-path. This contradicts N₂(t)=A∪B. Thus each member of M sees all other vertices of F. In particular M is a clique.

Choose any a₀∈A. We will find a spanning path in L=G[X∪U] starting at a₀ and ending at a vertex adjacent to M. The degrees in L satisfy

| Vertex | Degree in L | Reason |
|---|---:|---|
| x∈A | k−1 | Its outside neighbor is z. |
| p∈P | at least k−m | Only M can supply external neighbors. |
| r∈U | at least k−(v+m)≥a≥u+m | Only V∪M can supply external neighbors. |

First suppose u>0. Pick r₀∈U and augment L by a new vertex adjacent only to a₀ and r₀. The order is N=k+u+1. We apply the ordinary Bondy–Chvátal Hamilton-cycle closure, which allows adding a missing edge when its endpoint degrees sum to at least N.

1. The initially nonadjacent endpoints a₀,r₀ have degrees k and at least u+m+1. Add their edge. Now a₀ has degree at least k+1 and joins all U. Every member of U consequently gains a neighbor. The vertex r₀ has degree at least u+m+2 and joins every member of A.
2. Every member of U has degree at least u+m+1. Every member of P has degree at least k−m. Thus complete all U–P pairs. All of A has degree at least k, so complete all U–A pairs too.
3. To fill the remaining pairs in P, observe k≥u+2m because a≥u+m and b≥m. If k≥u+2m+1, then 2(k−m)≥N. Otherwise k=u+2m forces a=u+m and b=m. Each p now sees all of A∪U, and 2(a+u)≥N follows from u≥1. This completes P.
4. The only possible missing pairs in X∪U now lie within U. Each endpoint sees the k vertices of X, and 2k≥N as u≤a≤k−1.

The transformed graph is a clique on L with the degree-two marker. It has a Hamilton cycle, so the original augmentation does too. Removing the marker leaves a spanning a₀–r₀ path in L.

When u=0, choose any p₀∈P. If 2m<k then every vertex of X has degree at least k−m within X and 2(k−m)≥k+1. Add a degree-two marker at a₀,p₀ and use cycle closure to complete all of X, obtaining a spanning a₀–p₀ path as before. If 2m=k, then a,b≥m forces a=b=m. The complete bipartite subgraph between A and P has equal parts, so it has an alternating spanning path from a₀ to p₀. These are the only cases since 2m≤k.

Interchange the sides to obtain a spanning path of G[Y∪V] between b₀∈B and a vertex in V∪Q. Its nonanchor endpoint, like that of the left path, belongs to F and sees every member of M. Join the two nonanchor endpoints through the entire clique M in any order and close the cycle through b₀,z,a₀.

## The pure split

Now m=0. Both U,V are nonempty since every p and every q needs a remote neighbor. There is an edge r₀s₀ from U to V. Indeed, without one, deleting z separates X∪U from Y∪V. Choose r∈U,s∈V. All A lies at distance two from r through P. All B lies at distance four from r via z, and s lies at distance six via z. These are k+1 distinct other vertices at positive even distance, impossible.

Pick a₀∈A, b₀∈B. The preceding degree-two-marker construction in the u>0 case applies to L with m=0 and the chosen r₀. The same proof and inequalities hold (indeed k≥u+1). Obtain a spanning a₀–r₀ path in L and a spanning s₀–b₀ path in G[Y∪V]. The cross edge r₀s₀ and the two edges b₀z,za₀ finish the Hamilton cycle.

**Dependencies and scope.** This irregular theorem uses the classical Bondy–Chvátal cycle-closure lemma. Its initial ball decomposition follows from the elementary size count above. The regular ball theorem of Asratian–Granholm is unnecessary for this statement. To apply it to all regular graphs one additionally invokes their Theorem 1.6 and Lemma 2.2 for graphs with bounded second neighborhoods. For irregular graphs the presence of the split ball remains a hypothesis.

## A minimum-degree cut vertex of any radius-two ball

The same conclusion holds when the minimum-degree vertex z cuts a ball B₂(c) with possibly c≠z. The following transfer uses the counting argument of Asratian–Granholm, Lemma 2.2. Only z needs degree exactly k. Every other vertex needs degree at least k.

Suppose c≠z and let C be the component containing c in B₂(c)−z. A shortest c-to-vertex path of length at most two stays in the ball. Since some component separates from c, z must neighbor c, and every vertex of the ball outside C and different from z is a neighbor of z. Write D=N(z)∩C, p=|D|, and E=N(z)∖D, of size k−p. Thus 1≤p<k and B₂(c)∖(C∪{z})=E.

At least k−p neighbors of c lie outside the closed neighborhood N[z]: every neighbor of c lies in C∪{z}, where at most p choices lie in N[z] (z and D∖{c}). Let W be the neighbors of c outside N[z]. For any fixed x∈E, all its neighbors inside B₂(c) are in {z}∪(E∖{x}), of size k−p. Hence at least p of its neighbors, forming a set Y, are outside B₂(c). All vertices of W and Y lie at distance two from z, and W∩Y is empty. The cap forces |W|=k−p, |Y|=p and N₂(z)=W∪Y. In particular c has exactly k neighbors, including all of D∖{c}.

Now D∪W and E∪Y partition B₂(z)−z. There are no edges from D∪W to E because D∪W⊆C. Every member of D∪W is c or a neighbor of c, so none sees a vertex of Y outside B₂(c). Thus B₂(z)−z disconnects, as required.

For comparison, if the original conjecture has δ<σ=k, its unique vertex z of degree δ cannot cut *any* radius-two ball. For c=z the component lower bound k still holds because all neighbors of z have degree at least k, whereas |B₂(z)−z|≤δ+k<2k. For c≠z retain D,E,p above with |E|=δ−p. Both c and x∈E have degree at least k. The two disjoint subsets of N₂(z) then have sizes at least k−p and k−(δ−p), summing to 2k−δ>k. This rules out that case as well.

## General split centers

Let k=σ and δ≥2, and let z now be any cut vertex of its own induced radius-two ball. Write d=degree(z), let c≥2 be the number of components after deletion, and let aᵢ be the number of z-neighbors in component i. Each aᵢ is positive. A z-neighbor in component i sees the d−aᵢ neighbors in all other components at distance two, so aᵢ≥d−k, giving c(d−k)≤d.

If each component contains a z-neighbor of degree at least k, each has at least k vertices and ck≤d+k. These inequalities imply (c−1)²≤c, hence c=2. If a component contains no z-neighbor of degree k or greater, its sole z-neighbor must be the unique vertex of degree less than k. It sees d−1 other z-neighbors at distance two, forcing d≤k+1. Having c≥3 would then require at least 2k vertices in two other components and at least δ≥2 more in its own component. This exceeds d+k. Thus again c=2.

For the two components the anchor counts a,b are both at most k, so d≤2k. In a 2-connected graph both are in fact at most k−1. If for instance a=k, a vertex of the opposite anchor set B exhausts its full allowance on A at distance two. Inside its own connected component Y it must see every other vertex, since the first nonneighbor on a Y-path would give another distance-two vertex. Moreover Y has no neighbor outside B₂(z): the first exit, through a vertex of Y∖B, would give another distance-two vertex from B. Thus deleting z separates Y from the graph, contrary to 2-connectivity.

If δ=k then the sides have sizes k+i and k+j, with i,j≥0 and i+j≤d−k. Each z-neighbor on the first side misses at most i other vertices there, and analogously for the second side. The case d=k is exactly the complete-side-neighborhood theorem above.
