# Component counts across complete multipartite separators in Graph 189

Let $G$ be a finite simple 2-connected graph, and let $k$ be its second-smallest degree. Suppose every vertex has at most $k$ other vertices at even distance. Then

$$
c(G-S)\le |S|+1
$$

for every vertex set $S$ inducing a complete multipartite graph. There is no restriction on the number, sizes or induced graphs of the components of $G-S$.

## Counts for a minimal violating set

Suppose a complete multipartite $S$ violates the bound. Pass to an inclusion-minimal violating subset, which still induces a complete multipartite graph. The independent case is excluded by the [internal degree bound](independent-separators.md), so assume $G[S]$ has at least two parts. Write $s=|S|\ge2$, $c=c(G-S)\ge s+2$, and let $B$ be the outside vertices adjacent to $S$. At most one vertex $z$ has degree below $k$.

The [minimal-separator counts](independent-separators.md) show that every separator vertex meets at least three components, and a singleton component must be $z$. Every other component contains at least two vertices of $B$. In particular $|B|\ge2c-1$. They also show that some $u\in S$ has degree at least $k$ and has a neighbor of degree at least $k$ in every component it meets. Let $U$ be the set of all separator vertices with these two properties.

For $x\in B$, put $Q(x)=N(x)\cap S$, $q(x)=|Q(x)|$ and let $e(x)$ count the separator vertices at distance two from $x$. Say that $Q(x)$ dominates $G[S]$ when every vertex of $S\setminus Q(x)$ has a neighbor in $Q(x)$. If it dominates, $e(x)=s-q(x)$. A nonempty set fails to dominate this complete multipartite graph exactly when it is a proper subset of a single part $P$. In that case $e(x)\ge s-|P|$ from the other parts.

For $u\in S$ in a part of size $p$, write $d=\deg_{G[S]}(u)=s-p$ and $\ell=|\{v\in S:d_G(u,v)=2\}|=p-1$. The equality for $\ell$ holds because every pair in a part has a common neighbor in another part. If $u$ meets $t$ components, number those components from $1$ to $t$, and put $a_i=|N(u)\cap C_i|$ and $A=\sum_i a_i$. For a chosen neighbor $x_i$ of $u$ in $C_i$, the representative count from minimality, including all additional neighbors of $u$ in other components, gives

$$
q(x_i)+1+\sum_{j\ne i}(a_j-1)+e(x_i)\le k.
$$

If $x_i$ has degree at least $k$ and $X_i$ counts the vertices of $C_i$ at distance two from $u$, its internal neighbors give $a_i+X_i\ge k+1-q(x_i)$. If $u\in U$, these inequalities can be combined over all $t$ components to give

$$
\sum_i X_i \ge A+(t-3)(A-t)+\sum_i e(x_i).
$$

Since $A+d\ge k$ and $\ell+\sum_i X_i\le k$, this implies

$$
\ell+(t-3)(A-t)+\sum_i e(x_i)\le d.
$$

Thus every $x\in B$ of degree at least $k$ whose $Q(x)$ fails to dominate has all its separator neighbors outside $U$. Indeed, choosing $u\in Q(x)\cap U$ as above and taking $x_i=x$ in its component would give $\ell\ge1$ and $e(x)\ge d$, a contradiction.

## Counting from a separator vertex whose neighbors dominate

Let $u\in U$ and suppose every $x\in N(u)\cap B$ has $Q(x)$ dominating $G[S]$. Put $h=k-s$. The representative bound and $e(x)=s-q(x)$ yield $h\ge1$. Moreover, choosing each $x_i$ as above and summing the bounds on the extra neighbors gives

$$
A\le t+\frac{t}{t-1}(h-1)\le t+\frac32(h-1).
$$

Write $F_u=|\{x\in B:d_G(u,x)\ge3\}|$. If $X'$ consists of the vertices outside $S\cup B$ at distance two from $u$, then

$$
k\ge |B|-A-F_u+|X'|+\ell.
$$

In any component $C_i$ met by $u$, a chosen neighbor $x_i$ of degree at least $k$ has at least $h$ internal neighbors, of which at most $|B\cap C_i|-1$ are in $B$. Hence $|X'\cap C_i|\ge h+1-|B\cap C_i|$. The components not met by $u$ contain at least $2(c-t)-1$ boundary vertices. Combining these counts, when $h\ge2$,

$$
\begin{aligned}
F_u
&\ge t(h-2)+2c-1-\tfrac32(h-1)+\ell-k\\
&\ge s-\tfrac32+\tfrac h2+\ell.
\end{aligned}
$$

In particular there can be no such $u$ with $F_u=0$. For $h=1$ and $F_u=0$, the inequalities $A\le t\le c$, $|B|\ge2c-1$, and $k=s+1\ge |B|-A$ force $c=s+2$, $|B|=2c-1$ and $A=t=c$. There is a singleton component, which must be $z$, and $u$ meets every component. This contradicts $u\in U$, since $u$ then has only a below-$k$ neighbor in the singleton component. Thus the conclusion $F_u>0$ also holds when $h=1$.

## Locating the exceptional vertex

If there is no $z$, all separator vertices are in $U$, so all boundary neighborhoods dominate, which contradicts $F_u>0$. If $z\in S$, every other separator vertex belongs to $U$. Any boundary neighborhood failing to dominate must therefore be $\{z\}$. A separator vertex in a different part is in $U$, has only neighbors whose neighborhoods dominate, and has distance at most two to all of $B$. This is again impossible.

Now assume $z$ is outside $S$, in a component $C_z$. Any separator vertex outside $U$ is adjacent to $z$ and has no other neighbor in $C_z$. If $Q(z)$ is confined to a single part $P$, then every boundary neighborhood failing to dominate is confined to $P$, including $Q(z)$ if it fails to dominate. Any separator vertex in another part is in $U$, has only neighbors whose neighborhoods dominate, and is within distance two of all of $B$, again a contradiction.

We may therefore assume $Q(z)$ meets at least two parts and hence dominates. Every neighbor in $B$ of a separator vertex in $U$ has a neighborhood that dominates, and $h\ge1$ by the preceding count. For $h=1$, suppose some $x\in B$ has $Q(x)$ failing to dominate. Then $x$ has degree at least $k$, and any $u\in Q(x)$ lies outside $U$. This $u$ meets $C_z$ only in $z$, so that component contributes exactly one neighbor. In the remaining $t-1$ touched components choose neighbors of degree at least $k$, including $x$ in its component. Combining their corresponding inequalities gives

$$
\sum_{i:C_i\ne C_z}X_i\ge
(t-1)+(t-3)(A-t)+\sum_{i:C_i\ne C_z}e(x_i).
$$

For the part of $u$ of size $p$, we have $e(x)\ge s-p$ and $\ell=p-1$. It follows that $k\ge s+t-2$, and $k=s+1$ forces $t=3$ and equality. In the other touched component besides those of $z$ and $x$, the chosen neighbor $y$ has $e(y)=0$. This forces $Q(y)=S$, since $G[S]$ is connected and any edge from $Q(y)$ to its complement gives a separator vertex at distance two from $y$. But $Q(y)=S$ makes at least $2(c-1)-1\ge2s+1>k$ boundary vertices in other components have distance two from $y$. Thus $h=1$ allows no boundary neighborhood failing to dominate, contrary to $F_u>0$.

## The case $h\ge2$

Any $x\in B$ whose neighborhood fails to dominate has all separator neighbors outside $U$ and therefore adjacent to $z$. Such an $x$ lies outside $C_z$, since each of its separator neighbors meets $C_z$ only in $z$. Thus all these vertices are at distance two from $z$, and there are at most $k$ of them.

For a part $P$ containing $u\in U$, every boundary vertex at distance at least three from $u$ has its neighborhood confined to a proper subset of $P$. The lower bound on $F_u$ is positive, so $|P|\ge2$ and $\ell\ge1$. Such a part contributes at least $s-\tfrac12+\tfrac h2$ boundary vertices whose neighborhoods fail to dominate, and distinct parts contribute disjoint sets of vertices. Two such parts would contribute at least $2s-1+h>k$, contradicting the cap at $z$. Hence there is exactly one part $P$ meeting $U$. Also $F_u>0$ for $u\in P\cap U$ implies some vertex of $P$ lies outside $U$.

Every vertex of $S\setminus P$ is outside $U$ and therefore belongs to $Q(z)$. If any $x\in (B\cap C_z)\setminus\{z\}$ exists, it has degree at least $k$ and all its separator neighbors lie in $U$, since every separator vertex outside $U$ meets $C_z$ only in $z$. Such an $x$ must have a dominating neighborhood confined to $P$, so $Q(x)=P$. This contradicts $P\setminus U\ne\varnothing$. Therefore $B\cap C_z=\{z\}$, and 2-connectivity forces $C_z=\{z\}$.

Every other boundary neighborhood meets $Q(z)$. A neighborhood meeting $S\setminus P$ does so immediately. A neighborhood confined to $P$ either fails to dominate and has all its ports outside $U$, or equals $P$ and contains a vertex outside $U$. Consequently $|B|-1\le k$ by counting distance-two vertices from $z$. Now $k\ge2(c-1)\ge2s+2$, so $h\ge s+2$.

To finish, fix any $u\in S$, of internal degree $d$, and put $m=\lfloor(d+1)/2\rfloor$. Since $\deg_G(u)\ge k$ and $|B|\le k+1$, the vertex $u$ misses at most $d+1$ boundary vertices. Thus $u$ meets at least $s+1-m$ components other than $z$, as each missed component contains two or more boundary vertices. In each component it meets other than $z$, a neighbor of $u$ and its internal neighbors give at least $h+1$ vertices at distance one or two from $u$. Across these components there are at most $|B|-1\le k$ vertices at distance one from $u$, and at most $k-(s-1-d)=h+1+d$ at distance two, because all $s-1-d$ separator nonneighbors are at distance two. Therefore

$$
(s+1-m)(h+1)\le k+h+1+d,
\qquad
(s-1-m)h\le d+m.
$$

For $s\ge3$, this contradicts $h\ge s+2$, $d\le s-1$ and $m\le\lfloor s/2\rfloor$, as

$$
(s-1-\lfloor s/2\rfloor)(s+2)>s-1+\lfloor s/2\rfloor.
$$

For $s=3$ the two sides are $5$ and $3$, and for $s\ge4$ the inequality follows from $s^2-1>(s/2)(s+3)$. For $s=2$, every component meets both separator vertices, so the first inequality improves to $3(h+1)\le2h+4$, contrary to $h\ge4$. This excludes the remaining case.
