# Weighted Cartesian products with a bipartite factor

Let $H,F$ be finite simple connected graphs, with $|V(H)|\ge3$, and suppose $F$ is bipartite and has an edge. Replace each vertex of $H\square F$ by a nonempty graph of arbitrary size, joining fibers fully over each base edge and making no joins over base nonedges. Any such blow-up satisfying the Graph 189 even cap at its second-smallest degree $k$ has order at most $3k$. Thus the earlier order theorem through $3k+2$ gives a spanning path.

Distances between different fibers equal the base distances. Indeed a path projects to a base walk after stationary steps are removed, and shortest base paths lift using the complete joins. Cartesian distances add in the two coordinates, since every step changes exactly one coordinate, and shortest paths in the two factors can be concatenated.

Fix an edge $ab$ of $F$. At any $h\in V(H)$, choose roots in fibers $(h,a)$ and $(h,b)$. To any different base vertex other than these roots, exactly one of the two distances is positive even. The $H$ term is identical and the $F$ distances have opposite parity because $F$ is bipartite and $a,b$ are adjacent. Therefore if $n$ is the order of the blow-up and $s_h$ is the total weight of those two root fibers,
$$
n-s_h\le2k.
$$
For three distinct choices of $h$ the root pairs have disjoint fibers and their total weight is at most $n$. Summing gives $3n-n\le6k$, hence $n\le3k$.

For an explicit class of nontraceable bases, take the prism $K_{s,c}\square K_2$ with $s\ge3$ and $c\ge2s+2$. Each layer is a complete bipartite graph. It stays connected after deletion of fewer than $s$ vertices. After deletion of at most $s$ vertices in the prism, either both layers remain internally connected and at least one vertical matching edge survives, or one layer is intact and every surviving vertex of the other layer has its vertical neighbor there. The minimum degree is $s+1$, so the prism has connectivity exactly $s+1\ge4$.

Delete both copies of the smaller bipartition class. There remain $c$ connected leaf pairs. Consequently positive arbitrary fiber choices preserve nontraceability as long as the total order of the smaller-class fibers is at most $c-2$. Deletion of those fibers leaves more components than the number of deleted vertices plus one, which contradicts the component bound of any spanning path. This permits independent, unbounded integer weights on each leaf fiber and any admissible multiplicities on the smaller-class fibers. Nevertheless the parity-pair argument rules out every qualifying nontraceable choice. It also applies to prisms whose lack of a spanning path arises from a different certificate.
