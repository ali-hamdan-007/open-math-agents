# Separators of size at most four in Graph 189

Let $G$ be a finite simple 2-connected graph with second-smallest degree $k$. Suppose every vertex has at most $k$ other vertices at even distance. Then $c(G-S)\le |S|+1$ for every $S$ of size at most four.

Suppose otherwise and pass to a minimal violating subset. The [size-three result](matching-separators.md) gives $s=|S|=4$, so $c=c(G-S)\ge6$. If $\Delta(G[S])\le1$, the same matching-separator theorem excludes $S$. If $\Delta(G[S])=3$, a separator vertex dominates $G[S]$, which is impossible by the [dominating-vertex result](dominating-vertex-separators.md). Thus $\Delta(G[S])=2$, and the [strict internal degree bound](independent-separators.md) gives $k<8$.

As in the [internal degree bound](independent-separators.md), choose a separator vertex $u$ of degree at least $k$ with a neighbor $x_i$ of degree at least $k$ in every touched component $C_i$. Let $t$ count the touched components, $a_i=|N(u)\cap C_i|$, $A=\sum a_i$, $X_i=|\{x\in C_i:d_G(u,x)=2\}|$, and $X=\sum X_i$. Write $d=\deg_{G[S]}(u)$, let $\ell$ count the separator vertices at distance two from $u$, and put $q_i=|N(x_i)\cap S|$. The local counts give $t\ge3$, $A\le X\le k-\ell$, $k\le\ell+td/(t-2)$, and $a_i+X_i\ge k+1-q_i$. The [enhanced count](complete-multipartite-separators.md) also bounds $\sum e(x_i)\le d-\ell\le2$, where $e(x_i)$ counts the separator vertices at distance two from $x_i$. Hence some $x_i$ has $e(x_i)=0$. Its separator neighborhood contains the entire component of $G[S]$ containing $u$, since an edge of $G[S]$ from that neighborhood to its complement would supply a distance-two vertex.

No outside vertex can be adjacent to all of $S$. Such a vertex has at least $2(c-1)-1\ge9$ distance-two vertices from the outside boundary of the other components, since every nonsingleton component has at least two boundary vertices and at most one component is a singleton. This exceeds $k$. In particular $G[S]$ cannot be connected, by the choice with $e(x_i)=0$.

A disconnected graph on four vertices of maximum degree two has a component on three vertices and an isolate. The chosen separator vertex $u$ belongs to the three-vertex component, because an isolated vertex cannot satisfy $k\le4d$. Thus the choice with $e(x_i)=0$ has $q_i=3$. Every component meets this separator neighborhood, since a component needs at least two distinct neighbors in $S$ and the neighborhood leaves only one vertex of $S$ outside. The even-distance count from $x_i$ then gives $k\ge c-1\ge5$. Consequently $d=2$, since $k\le4d$, and $\ell\le1$ because $u$ has only one separator nonneighbor.

All chosen $q_i$ are at most three, and therefore

$$
t(k-2)\le A+X\le 2(k-\ell).
$$

With $k\ge5$ and $t\ge3$, this rules out $\ell=1$. With $\ell=0$ it implies $k\le6$ and $t=3$. For any $i$ with $q_i=3$, every other component contributes a representative at distance two, as above. In the other components meeting $u$, the representatives can be chosen among the neighbors of $u$, and all the additional such neighbors are also at distance two. Therefore

$$
k\ge c-1+\sum_{j\ne i}(a_j-1)\ge5+A-a_i-2.
$$

If $k=6$, the inequality $A+X\ge12$ forces $A=X=6$, and $a_i+X_i\ge k+1-q_i$ forces all three $q_i=3$. The last displayed bound then gives $a_i\ge3$ for all three indices, contradicting $A=6$.

If $k=5$, the lower bound $A+X\ge9$ with $A\le X\le5$ gives $A=4$ or $A=5$. In the first case $A+X=9$, so all three $q_i=3$. In the second case $A+X=10$, so at least two $q_i=3$, since each $q_i\le2$ would increase the contribution $k+1-q_i$ above three. For both cases, the displayed bound for two indices with $q_i=3$ gives $a_j=1$ for all three indices. This contradicts $A\ge4$.
