# A dominating vertex in a minimal separator in Graph 189

Let $G$ be a finite simple 2-connected graph, and let $k$ be its second-smallest degree. Suppose every vertex has at most $k$ other vertices at even distance. If $S$ is inclusion-minimal with $c(G-S)\ge |S|+2$, then $G[S]$ has no dominating vertex.

Suppose otherwise and let $u$ be adjacent to all of $S\setminus\{u\}$. Write $s=|S|\ge2$, $c=c(G-S)\ge s+2$ and $h=k-s$. Let $B$ be the outside vertices with a neighbor in $S$. By the [minimal-separator counts](independent-separators.md), at most one component of $G-S$ is a singleton, and every other component contains at least two vertices of $B$.

Number the $t$ components containing a neighbor of $u$, write $a_i=|N(u)\cap C_i|$ for those components, and put $A=\sum_i a_i$. Minimality gives $t\ge c+1-s\ge3$. Every neighbor $x$ of $u$ in a touched component has distance at most two to all of $S$, since $u$ dominates $G[S]$. As in the [boundary-distance proof](clique-separators.md), the representative count gives $h\ge1$ and

$$
\sum_{j\ne i}(a_j-1)\le h-1
\quad\text{for every }i,\qquad
A\le t+\frac32(h-1).
$$

The vertex $u$ also lies within distance two of every vertex in $B$. If $X$ is the set of vertices outside $S\cup B$ at distance two from $u$, then $k\ge |B|-A+|X|$.

## The case $h=1$

We have $A\le t\le c$ and $|B|\ge2c-1$. This gives

$$
k\ge |B|-A+|X|\ge c-1+|X|\ge s+1+|X|=k+|X|,
$$

so $X$ is empty, $c=s+2$, $|B|=2c-1$, and $A=t=c$. Thus $u$ has exactly one neighbor $x_i$ in each component. There is exactly one singleton component, and every nonsingleton component has exactly two boundary vertices.

The representative count from each $x_i$ already supplies $s+1=k$ vertices at distance two from $x_i$ in $S$ and in other components. Thus $x_i$ has no vertex of $C_i$ at distance two, so $x_i$ is adjacent to every other vertex of $C_i$. Indeed, an internal shortest path from $x_i$ to a nonneighbor in the connected component would supply a vertex at distance two. This makes every vertex of $C_i\setminus B$ lie at distance two from $u$, contrary to $X=\varnothing$. Consequently the nonsingleton components all have order two. The singleton has the only degree below $k$ by the minimal-separator count, so both vertices in each order-two component have degree at least $k=s+1$. Each must be adjacent to all of $S$, contrary to $a_i=1$.

## The case $h\ge2$

Let $r$ be the number of components in which $u$ has a neighbor of degree at least $k$. Then $r\ge t-1\ge2$. For each one, choose a neighbor $x\in C_i$ of $u$ of degree at least $k$. The vertex $x$ has at least $h$ neighbors inside $C_i$. Of those, at most $|B\cap C_i|-1$ are in $B$, so $|X\cap C_i|\ge h+1-|B\cap C_i|$. Outside these $r$ components there are at least $2(c-r)-1$ vertices of $B$. Since $t\le r+1$, the estimates combine to give

$$
\begin{aligned}
k&\ge |B|-A+|X|\\
 &\ge r(h-2)+2c-2-\tfrac32(h-1).
\end{aligned}
$$

If $r\ge3$, the last expression is at least $k+s-\tfrac52+\tfrac h2>k$. If $r=2$, it is at least $k+s-\tfrac12-\tfrac h2$, so $h\ge2s-1$ and $k\ge3s-1$.

On the other hand, the [internal degree bound](independent-separators.md) supplies a separator vertex $v$ of internal degree $d$ meeting $t_v\ge3$ components, with

$$
k\le \ell + \frac{t_v}{t_v-2}d,
$$

where $\ell$ counts the separator vertices at distance two from $v$. The dominating vertex $u$ guarantees that every separator nonneighbor of $v$ is at distance two, so $\ell=s-1-d$. Hence $k\le s-1+2d\le3s-3$, contradicting $k\ge3s-1$.
