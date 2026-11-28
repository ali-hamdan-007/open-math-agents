# Component counts across clique separators in Graph 189

Let $G$ be a finite simple 2-connected graph, and let $k$ be its second-smallest degree. Suppose every vertex has at most $k$ other vertices at even distance. For every clique $S\subseteq V(G)$,

$$
c(G-S)\le |S|+1.
$$

More generally, let $S$ be an inclusion-minimal set with $c(G-S)\ge |S|+2$, and let $B$ consist of the vertices outside $S$ with a neighbor in $S$. Then some $u\in S$ and $x\in B$ have $d(u,x)\ge3$. In particular, some nonempty set $N(x)\cap S$ fails to dominate $G[S]$.

## Incidence bounds for a minimal separator

Write $s=|S|$, $c=c(G-S)$ and $C_1,\ldots,C_c$ for the components. By 2-connectivity, $s\ge2$. For any proper subset $T\subsetneq S$, at most $|T|$ components of $G-S$ have all their neighbors in $T$. Each such component survives as a component of $G-T$, and at least one more component of $G-T$ contains a vertex of $S\setminus T$. Minimality gives $c(G-T)\le |T|+1$.

Take $x\in B\cap C_i$, and put $Q=N(x)\cap S$ and $q=|Q|$. At least $c-(s-q)-1\ge q+1$ other components have a neighbor in $Q$. Each supplies a distinct vertex at distance two from $x$. Consequently $q\le k-1$, and any singleton component has degree below $k$. There is at most one such singleton, because there is at most one vertex of degree below $k$. Every nonsingleton component has at least two vertices in $B$, since its sole vertex in $B$ would otherwise be a cut vertex. Separately, each component meets at least two distinct separator vertices via edges, since one such separator vertex would be a cut vertex.

Every $u\in S$ meets at least three components. Indeed, if $u$ meets $t$ components, then adding $u$ back to $G-S$ leaves $c+1-t$ components. Minimality gives $c+1-t\le s$, so $t\ge c+1-s\ge3$.

## Distance at most two across the boundary

Assume $d(u,x)\le2$ for every $u\in S$ and $x\in B$. For the $x,Q,q$ above, all $s-q$ vertices of $S\setminus Q$ are at distance two from $x$. Along with one representative from each of the other components meeting $Q$, this supplies at least $c-1\ge s+1$ even-distance vertices. Set $h=k-s\ge1$.

Fix $u\in S$ and let $a_i=|N(u)\cap C_i|$, $t=|\{i:a_i>0\}|$ and $A=\sum_i a_i$. For any $i$ with $a_i>0$, choose $x\in N(u)\cap C_i$. The representatives for the other components meeting $Q$ can be chosen in $N(u)$ wherever $a_j>0$, because $u\in Q$. The additional $a_j-1$ neighbors of $u$ in each such other component are also at distance two from $x$, so

$$
\sum_{j\ne i,\ a_j>0}(a_j-1)\le h-1.
$$

Summing over the $t$ choices gives

$$
A\le t+\frac{t}{t-1}(h-1)\le t+\frac32(h-1).
$$

Write $b_i=|B\cap C_i|$. Let $X$ be the vertices of $V(G)\setminus (S\cup B)$ at distance two from $u$. Every boundary vertex outside $N(u)$ is at distance two from $u$, giving

$$
k\ge |B|-A+|X|.
$$

Discard the component containing the possible vertex of degree below $k$, if it is outside $S$. The remaining at least $c-1\ge s+1$ components each meet at least two separator vertices. Some $u\in S$ thereby meets at least three of these components. For this $u$, let $r\ge3$ count all components in which $u$ has a neighbor of degree at least $k$. Then $t\le r+1$, since at most one component can have only a neighbor below degree $k$. In each of those $r$ components $C_i$, choose a neighbor $x$ of $u$ of degree at least $k$. The vertex $x$ has at least $k-s=h$ neighbors inside $C_i$, of which at most $b_i-1$ lie in $B$. All the other neighbors of $x$ inside $C_i$ lie in $X$, so $|X\cap C_i|\ge h+1-b_i$.

Outside these $r$ components there are at least $2(c-r)-1$ boundary vertices, as at most one component is a singleton. It follows that

$$
\begin{aligned}
k &\ge |B|-A+|X|\\
  &\ge 2(c-r)-1 -\left(r+1+\tfrac32(h-1)\right)+r(h+1)\\
  &=r(h-2)+2c-2-\tfrac32(h-1).
\end{aligned}
$$

If $h\ge2$, then $r\ge3$, $c\ge s+2$ and $k=s+h$ make the last quantity at least $k+s-\tfrac52+\tfrac h2>k$, a contradiction.

If $h=1$, the bound on $A$ applies to every $u\in S$ and gives $A\le t\le c$. As $|B|\ge2c-1$,

$$
s+1=k\ge |B|-A+|X|\ge c-1+|X|\ge s+1+|X|.
$$

All inequalities are equalities for every $u\in S$. In particular $c=s+2$, $|B|=2c-1$, every $u$ has exactly one neighbor in $B\cap C_i$ for every $i$, and each $X$ is empty. If any vertex were outside $S\cup B$, a shortest path from it to $S$ would include a vertex outside $S\cup B$ at distance two from a separator vertex. Hence $B=V(G)\setminus S$. The boundary count now implies exactly one singleton component and $c-1$ components of size two. The singleton uses the only possible degree below $k$. Both vertices in any size-two component therefore have at least $k-1=s$ neighbors in $S$, contradicting the exactly-one-neighbor count.

This proves the asserted distance constraint on a minimal obstruction. For an arbitrary clique $S$ violating the component bound, an inclusion-minimal violating subset would still be a clique. Its separator and boundary vertices would all be at distance at most two, which has just been excluded.
