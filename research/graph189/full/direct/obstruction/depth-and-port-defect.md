# Distance-four counts across a minimal violating separator

Let $G$ be a finite simple 2-connected graph satisfying the Graph 189 bound on even-distance counts, let $k$ be its second-smallest degree, and let $S$ be inclusion-minimal with $c(G-S)\ge |S|+2$. Use the established Graph 189 distance lemma that two vertices of degree at least $k$ have distance at most four. Call such vertices high, and write $s=|S|$, $c=c(G-S)$. Then every high vertex outside $S$ has distance one or two from $S$, and every high vertex adjacent to $S$ has at most $k-2$ neighbors in $S$.

## Vertices at distance two from the separator

At least $s+1$ components of $G-S$ consist entirely of high vertices. Each has size at least $m=\max(2,k+1-s)$ by the [incidence bounds](independent-separators.md). If a high vertex $x$ has distance at least three from $S$, it has distance at least four to every high vertex in any different component. The high-endpoint distance bound therefore puts them all at distance four from $x$. At least $s$ of the wholly high components are different from the component of $x$, giving $sm$ even-distance vertices. If $k\le s$, then $sm\ge2s>k$. If $k>s$, then $s(k+1-s)-k=(s-1)(k-s)>0$. Either way the cap is exceeded.

Now let a high vertex $x$ have distance two from $S$, let $U=\{p\in S:d_G(x,p)=2\}$, and let $M$ count all high vertices in components different from the component of $x$. Every such vertex $y$ has distance three or four from $x$. It has distance three exactly when it is adjacent to a vertex of $U$. Indeed, a geodesic of length three to a foreign component must first go from $x$ to a neighbor in its own component, then to $S$, and then to $y$.

For each $p\in U$, choose a common neighbor of $x$ and $p$ in the component of $x$. Every $p$-neighbor in a foreign component lies at distance two from that chosen neighbor, so there are at most $k$ of them. Thus at most $k|U|$ of the $M$ foreign high vertices are at distance three from $x$. At most $k-|U|$ others are at distance four from $x$, because the vertices of $U$ themselves lie at distance two. Consequently

$$
M\le (|U|+1)k-|U|.
$$

In particular, if $t\ge2$ components contain a high vertex at distance two from $S$, then each such vertex has $|U|\ge t-1$. To see this, its $t-1$ other components each have size at least $k+1$, since a high vertex at distance two from $S$ has all its neighbors within its component. There is at most one low vertex globally, so $M\ge(t-1)(k+1)-1$. For $t=2$ the claim follows simply from the existence of a shortest path to $S$. For $t\ge3$, substituting $|U|\le t-2$ in the upper bound gives $M\le(t-1)k-(t-2)$, strictly smaller than the lower bound.

## High vertices with many separator neighbors

Let $x$ be a high vertex adjacent to $S$, in component $C$, and let $Q=N(x)\cap S$, $q=|Q|$, and $P=\{p\in S:d_G(x,p)=2\}$. At least $q+2$ components meet $Q$ by minimality, where a component meets a separator set if some vertex in the component has a neighbor in the set. Let $c_Q$ be this number. Representatives from the $c_Q-1$ other components meeting $Q$ give distinct vertices at distance two from $x$.

If a component $C'$ does not meet $Q$, a high vertex $y$ in $C'$ is at distance three from $x$ exactly when it is adjacent to a vertex of $P$. In fact, the penultimate vertex on a geodesic of length three must lie in $S$: a penultimate vertex outside $S$ would lie in $C'$, and its distance two from $x$ would force $C'$ to meet $Q$. Thus every high vertex in a component not meeting $Q$ and having no neighbor in $P$ lies at distance four from $x$. Let $F$ be the set of those vertices. The disjoint even-distance witnesses give

$$
(c_Q-1)+|P|+|F|+|\{y\in C:d_G(x,y)=2\}|\le k.
$$

In particular, if $q=k-1$, then $c_Q=k+1$ and $P=F=\varnothing$. Each component not meeting $Q$ then contains no high vertex, so there is at most one such component, and it would have to be a low singleton. Hence $c\le k+2$ and $k-1\le s\le k$.

If $s=k$, then $S\setminus Q$ has one vertex. Every component meets $Q$, because each needs at least two distinct neighbors in $S$. This gives $c=c_Q=k+1$, contrary to $c\ge s+2$. If $s=k-1$, then $Q=S$. Each component other than $C$ has exactly one vertex adjacent to $S$, because all even-distance capacity of $x$ is used by one representative per other component. A nonsingleton component needs at least two vertices adjacent to $S$ by 2-connectivity, and at most one component is a singleton. This is again impossible. Consequently $q\le k-2$.
