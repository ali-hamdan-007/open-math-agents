# Diameter-five exclusion through minimum degree four

This is a handwritten proof. Use the hypotheses and notation of [diameter-five-low.md](diameter-five-low.md). In particular, we assume 2-connectivity and the condition on the endpoints of every distance-five pair appearing in the merged OMA reduction. The conclusion is that $\delta(G)\ge5$.

The following counting bounds apply at any minimum degree $k$. We have $r\ge2$, $w\ge\sigma-k$, $w+u\le\sigma$, $t\ge w+1$, and $t\le\sigma-2$. All vertices of $T$ are at distance four from every vertex of $A$. Every vertex of $W$ has a neighbor in $A$, and every vertex of $R$ has a neighbor in $W$.

## Complete incidence between $A$ and $W$ is impossible

If every anchor is adjacent to every vertex of $W$, then every vertex of $R$ has all $k$ anchors at distance two, and the cap at any anchor gives $r\le\sigma-t$. Since $t\ge w+1\ge\sigma-k+1$, any $v\in R$ fails to have at least one vertex $y\in T$ at distance two. Such a $y$ has no edge to any neighbor of $v$ in $U$. The degree lower bound at $y$ means it misses at most $\beta=u+t-1-\sigma$ potential neighbors in $U\cup(T\setminus\{y\})$. Therefore $v$ has at most $\beta$ neighbors in $U$. The only other possible neighbors of $v$ lie in $W\cup(R\setminus\{v\})$, so
$$
\deg(v)\le w+r-1+\beta
\le w+(\sigma-t)-1+(u+t-1-\sigma)
=w+u-2\le\sigma-2.
$$
This contradicts the minimum degree of a vertex other than $x$. In particular $w\ne\sigma-k$, since equality would force every possible anchor edge by degree. This argument is due to the diameter-five layer worker and also holds without 2-connectivity.

## Minimum degree four

By [diameter-five-low.md](diameter-five-low.md) we may assume $k=4$. The bounds above and the exclusion of $w=\sigma-k$ force $w=\sigma-3$ and $t=\sigma-2$. From $w+u\le\sigma$ and $u+t-1\ge\sigma$ we get $u=3$. Every far vertex is adjacent to all of $U$, since it has degree at least $\sigma$ and at most $u+t-1=\sigma$ possible neighbors.

Each anchor has $k+w=\sigma+1$ possible neighbors, so it misses at most one of them. If two anchors were nonadjacent, they would each see all of $W$. At either anchor, the other would lie at distance two through $x$, as would all $r\ge2$ vertices of $R$ through $W$. Together with the $t=\sigma-2$ vertices at distance four, this exceeds the positive even-distance cap. Thus the anchors form a clique. Any miss in $W$ therefore contributes a distance-two vertex at the anchor that misses it.

There are at least two vertices of $R$ with a neighbor in $U$, since otherwise a single vertex would separate $x$ from $T$. Any such $v$ sees all $t=\sigma-2$ far vertices at distance two through its neighbor in $U$, so at most two anchors are at distance two from $v$. Every anchor that sees a neighbor of $v$ in $W$ is at distance two from $v$, so at least two anchors miss all its neighbors in $W$. Since each anchor misses at most one vertex of $W$, $v$ has a unique neighbor there, which is missed by at least two anchors.

Select two vertices $v_1,v_2\in R$ that have a neighbor in $U$. If they have the same sole neighbor $p$ in $W$, choose an anchor seeing $p$. Both $v_1,v_2$ and all of $T$ exhaust its cap, so this anchor cannot miss any vertex of $W$. It therefore reaches all of $R$ at distance two, forcing $R=\{v_1,v_2\}$. Deleting $p$ removes every edge from $W$ to $R$, disconnecting $x$ from $T$. This contradicts 2-connectivity.

If the sole $W$-neighbors $p,q$ of $v_1,v_2$ are distinct, each is missed by at least two anchors. Their sets of missing anchors are disjoint since each anchor may miss at most one vertex of $W$. Thus each is seen by exactly two anchors, and each anchor sees exactly one of $p,q$. Each anchor now counts one missed $W$-vertex and one of $v_1,v_2$ at distance two, together with all of $T$ at distance four. No additional vertex of $R$ is possible because each has a neighbor in $W$ and hence is at distance two from some anchor. Thus $R=\{v_1,v_2\}$. The degree of $p$ is at most $2+(w-1)+1=w+2=\sigma-1$, since it sees only two anchors and only $v_1$ among the remotes. This again contradicts the degree lower bound.
