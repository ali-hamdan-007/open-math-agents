# Separators inducing a matching and isolated vertices in Graph 189

Let $G$ be a finite simple 2-connected graph with second-smallest degree $k$. Suppose every vertex has at most $k$ other vertices at even distance. Then $c(G-S)\le |S|+1$ whenever $\Delta(G[S])\le1$. In particular no set of at most three vertices violates the component bound.

Suppose there is a violating set and take an inclusion-minimal one, still with $\Delta(G[S])\le1$. Use the notation and the [incidence bounds](independent-separators.md) for such a set. In particular every separator vertex meets at least three components, and a boundary vertex with $q$ neighbors in $S$ has at least $q+1$ other components supplying distance-two vertices. Let $U$ be the separator vertices of degree at least $k$ having a neighbor of degree at least $k$ in every component they meet. The internal degree proof shows $U\ne\varnothing$. As in the [multipartite proof](complete-multipartite-separators.md), if $a_i=|N(u)\cap C_i|$ in the $t$ components met by $u$, $A=\sum a_i$, and $u\in U$, choose a neighbor $x_i$ of degree at least $k$ in each such component. Let $q_i=|N(x_i)\cap S|$, let $e_i$ count the separator vertices at distance two from $x_i$, and let $X$ count the vertices in the touched components at distance two from $u$. Writing $d$ for the internal degree of $u$ and $\ell$ for the number of separator vertices at distance two from $u$, the two counts give

$$
\ell+\sum_i e_i+(t-3)(A-t)\le d,\qquad
t(k-d-\ell)\le A+X,\qquad
A\le X\le k-\ell,\qquad q_i\le1+d+\ell.
$$

Also $a_i+X_i\ge k+1-q_i$, where $X_i$ is the contribution of $C_i$ to $X$. If $u$ instead has only the unique vertex $z$ of degree below $k$ in one touched component, choose neighbors of degree at least $k$ in each of the other $t-1$ touched components and let $X$ count the distance-two vertices in those components. The $t-1$ version of the count is

$$
X\ge (t-1)+(t-3)(A-t)+\sum_i e_i.
$$

In particular $X\ge A-1$ when $t\ge4$.

Take $u\in U$. The [internal degree bound](independent-separators.md) gives $k\le4d$, and $A\ge t\ge3$ gives $k\ge3$. Thus $d=1$ and $k\in\{3,4\}$. Write $v$ for the unique neighbor of $u$ in $S$.

## The case $k=4$

The bound $k\le\ell+td/(t-2)$ with $\ell\le d=1$ forces $\ell=1$ and $t=3$. Then $A=X=3$ and the three inequalities $a_i+X_i\ge k+1-q_i$ force $q_i=3$ in every touched component, because each $q_i\le3$ and $A+X=6$. Each component contains exactly one neighbor of $u$. Its separator neighborhood triples are all $\{u,v,w\}$, where $w$ is the unique separator vertex at distance two from $u$. Since $\ell=d$, the enhanced count gives $e_i=0$ for all three neighbors. The vertex $w$ is isolated in $G[S]$, since its potential neighbor would be outside $\{u,v,w\}$ and hence at distance two from each of the three neighbors of $u$.

As $w$ is isolated in $G[S]$, the internal degree bound shows $w\notin U$. If $w$ has degree below $k$, its three shared neighbors exhaust its degree, so it meets exactly the three components met by $u$. Also $v\in U$ in this case, since $w$ is the only vertex of degree below $k$. The common neighbors give $d_G(v,w)=2$, and the same bounds for $v$ give $A_v\le k-1=3$. Hence all three vertices $u,v,w$ together meet only three components. This contradicts the lower bound of at least five components meeting the separator neighborhood of any of the three neighbors of $u$.

If $w$ has degree at least $k$, it is outside $U$ only because it meets the component containing the low-degree vertex $z$ solely through $z$. That component differs from the three already met by $w$, since each of those contains a shared neighbor of degree at least $k$. Thus $w$ meets at least four components. Its outside degree $A_w$ is at least $k$, since it has internal degree zero. The count with one low-degree neighbor gives $X_w\ge A_w-1\ge k-1$. The two vertices $u,v$ are both at distance two from $w$ via their shared neighbors, so $w$ exceeds the even-distance cap.

## The case $k=3$

Since $A\ge t\ge3$ and $A\le k-\ell$, we have $\ell=0$ and $A=X=t=3$. Each $q_i=2$ by $a_i+X_i\ge k+1-q_i$ and $q_i\le2$. Thus each touched component contains exactly one neighbor of $u$, and each such neighbor has separator neighborhood $Q=\{u,v\}$. At least four components meet $Q$ by the representatives bound. At most four do, since each one other than the component of a neighbor of $u$ contributes a vertex at distance two from that neighbor. Therefore $v$ meets an additional fourth component, which $u$ misses.

The vertex $v$ has degree at least $4$, since it sees $u$ and their three shared neighbors. If $v\in U$ it would have outside degree at most $3$, which would exclude the fourth component. Thus $v$ meets the fourth component only through the vertex $z$ of degree below $k$. The other three components already contain their shared neighbors of degree at least $k$, so none of those is the fourth component. The count with one low-degree neighbor yields $X_v\ge A_v-1\ge3$ in these other three components. This saturates the even-distance cap at $v$, so no separator vertex is at distance two from $v$. The only possible separator neighbors of $z$ are therefore $v$ and the internal neighbor $u$ of $v$. But $u$ misses the fourth component, so $z$ is adjacent only to $v$ in $S$. By 2-connectivity, $z$ has a second neighbor, which is in its own component and is at distance two from $v$ through $z$. This contradicts the saturation at $v$.

Finally an inclusion-minimal violating set of size two or three either induces a graph of maximum degree at most one or has a dominating vertex, which the [dominating-vertex result](dominating-vertex-separators.md) excludes.
