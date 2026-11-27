# Diameter five forces minimum degree at least four

This is a handwritten argument. It is independent of profile enumeration.

Let $G$ be a finite simple 2-connected graph of diameter five, and let $\sigma$ be its second-smallest degree. Suppose every vertex has at most $\sigma+1$ vertices at even distance, including itself. Suppose further that whenever $\operatorname{dist}(v,w)=5$, at least one of $v,w$ has degree less than $\sigma$. This last property is a hypothesis of the merged OMA reduction $\mathrm{R1.H2}$; in its parent it is derived from the original even-distance hypothesis. Then $\delta(G)\ge4$.

Choose vertices $x,y$ at distance five. We may assume $\deg(x)<\sigma$. Since $\sigma$ is the second-smallest degree, $x$ is the unique vertex with degree below $\sigma$. Put $k=\deg(x)=\delta(G)$. Write $A,W,R,U,T$ for the layers at distances $1,2,3,4,5$ from $x$, and $w,r,u,t$ for the sizes of $W,R,U,T$. The layers partition the vertices other than $x$. Since $R$ separates $x$ from $T$, 2-connectivity gives $r\ge2$.

Every $a\in A$ has potential neighbors in $\{x\}\cup(A\setminus\{a\})\cup W$ and degree at least $\sigma$. Hence $w\ge \sigma-k$. The even-distance cap at $x$ gives $w+u\le\sigma$. Every vertex of $T$ has potential neighbors in $U$ and in the rest of $T$, so $\sigma\le u+t-1$. Together these yield $t\ge w+1$.

For every $a\in A$ and $v\in T$, the triangle inequality gives $\operatorname{dist}(a,v)\ge4$. The diameter-five pair assumption and $\deg(a),\deg(v)\ge\sigma$ give $\operatorname{dist}(a,v)\ne5$, so $\operatorname{dist}(a,v)=4$. A shortest $a$-$v$ path prefixed by $x,a$ has length five and is a shortest $x$-$v$ path. Its distance-three vertex from $x$ is at distance two from $a$. Thus every anchor has all $t$ vertices of $T$ at distance four and at least one vertex of $R$ at distance two. Its even-distance cap yields $t\le\sigma-1$.

In fact $t\le\sigma-2$. If $t=\sigma-1$, an anchor's only positive even-distance allowance outside $T$ is already taken by a vertex of $R$. Every nonadjacent anchor pair would give a further distance-two vertex via $x$. Thus $A$ is a clique. If some anchor missed a vertex of $W$, that vertex has another anchor as a neighbor by the layer definition and would be a further distance-two vertex from the anchor that misses it. Hence every anchor sees all of $W$. Then all of $R$ is at distance two from every anchor, since all vertices of $R$ have a neighbor in $W$. This contradicts $r\ge2$.

Combining the inequalities gives
$$
\sigma-k\le w\le t-1\le\sigma-3.
$$
This excludes $k\le2$. If $k=3$, equality forces $w=\sigma-3$ and $t=\sigma-2$. All neighbors of an anchor lie among exactly $k+w=\sigma$ possibilities, so the degree lower bound forces every anchor adjacent to all of $W$. Also $u+t-1\ge\sigma$ gives $u\ge3$, while $w+u\le\sigma$ gives $u\le3$. Thus $u=3$ and every far vertex is adjacent to every vertex of $U$, by its degree lower bound and $u+t-1=\sigma$. Choose an edge between $R$ and $U$, which exists on any shortest $x$-$y$ path. Its endpoint in $R$ has all three anchors at distance exactly two through a predecessor in $W$, and all $t=\sigma-2$ far vertices at distance exactly two through its neighbor in $U$. The layers preclude adjacency to these witnesses. This gives $\sigma+1$ vertices at positive even distance, exceeding the cap of $\sigma$. Therefore $k\ne3$, proving the result.
