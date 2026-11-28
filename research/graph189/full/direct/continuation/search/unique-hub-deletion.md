# Deleting the unique vertex above the second-smallest degree

Let $G$ satisfy Graph 189, with order $n$ and second-smallest degree $k$. Suppose it has one vertex $h$ of degree above $k$, and that all other vertices have degree $k$ except for at most one vertex $z$ of lower degree. If there is no lower-degree vertex, choose any vertex other than $h$ as $z$. Then $G$ is traceable at every order $n\ge4k+1$. If $\deg(h)=k+1$, it is traceable at every order. In a counterexample with $k\ge13$ and any hub degree, the connectivity is two, and every separating pair contains $h$.

We may use the established cut-vertex, small-$k$, and $n\le3k+2$ results. In particular, work in a putative 2-connected counterexample of order $n>3k+2$ and with $k\ge6$.

## The exact-degree path criterion after deleting the hub

Use the [rooted local Ore count](../root/rooted-local-ore.md) and the [wedge inequality](../verify/wedge-order-and-hamiltonicity.md). For an induced wedge $u,w,v$ in $G$, write

$$
j_G(u,w,v)=|N_G(u)\cup N_G(w)\cup N_G(v)|-\deg_G(u)-\deg_G(v),
$$

and let $e(w)$ count the positive even-distance vertices from $w$. The wedge bound is

$$
(k+1)j_G(u,w,v)
\le3k+2-n+k(1+\deg_G(w)+e(w)-\deg_G(u)-\deg_G(v)).
$$

Let $H=G-h$, which is connected. For induced wedges of $H$ with endpoints other than $z$, the endpoints have degree $k$ in $G$ and the center has degree at most $k$ in $G$. Hence $j_G\le0$ at $n>3k+2$. Removing $h$ decreases the neighborhood union by one if $h$ belonged to it and also decreases each of the endpoint degrees by one if the endpoint was adjacent to $h$. Thus $j_H\le j_G+1\le1$. Equality $j_H=1$ requires $j_G=0$ and both endpoints adjacent to $h$ in $G$. The wedge inequality and $n>3k+2$ then require $\deg_G(w)=e(w)=k$.

Take a longest path in $H$ starting at $z$. If it spans $H$, the [almost-spanning result](../lowblock/all-near-spanning.md) gives traceability of $G$. Otherwise take any exterior vertex $u$ with at least one path neighbor. Let $W$ be its path neighbors and $U$ their successors. The rooted Ore count in $H$ gives

$$
\sum_{w\in W}j_H(u,w,s(w))\ge |W|.
$$

Thus every one of these wedges has $j_H=1$ and therefore has $j_G=0$, both endpoints adjacent to $h$, and center degree and positive-even count equal to $k$ in $G$. In particular all exterior vertices of $H$ touching the path and all successors of their contact positions lie in $N_G(h)$. If $z$ has degree below $k$, it has no exterior neighbor in this path configuration because it cannot be the center of an equality wedge.

The individual rooted lower bounds at all marks are equalities as well. In the notation of the rooted proof, for every $w\in W$,

$$
N_H(w)\setminus\bigl(N_H(u)\cup N_H(s(w))\bigr)
=\{u\}\cup\bigl(N_H(w)\cap U\bigr).
$$

Consequently each contact position $w$ meets just one exterior component, and its exterior neighbors induce a clique. Indeed, $w$ and $s(w)$ cannot both meet any one exterior component, because a path through that component would extend the rooted path. If $w$ had a neighbor outside the component of $u$, this neighbor would lie in the displayed set outside the path and differ from $u$. Within the component of $u$, any other neighbor of $w$ must be adjacent to $u$ for the same reason. Since $u$ can be any exterior neighbor of $w$, the clique claim follows.

## The order bound

Assume $n\ge4k+1$ and fix one equality wedge $u,w,v$ above. In the [proof of the wedge inequality](../verify/wedge-order-and-hamiltonicity.md), let

$$
Q=N_G(w)\setminus\bigl(N_G(u)\cup N_G(v)\bigr),
\qquad
C_1=N_G(u)\cap N_G(w)\cap N_G(v).
$$

Let $T$ be the set of vertices whose three distances from $u,w,v$ are odd and equal to at least three. The wedge proof gives $|T|\ge n-3k-2$ because $j_G=0$, and its possible penultimate vertices on shortest paths from $w$ to $T$ have total number

$$
1+\deg_G(w)+e(w)-\deg_G(u)-\deg_G(v)-j_G=1.
$$

Write $a$ for this unique penultimate vertex. It must be at distance two from $w$. Otherwise each vertex of $T$ would have distance at least five from the high vertex $w$, leaving at most the sole low vertex in $T$ by the high-endpoint distance bound. But $|T|\ge n-3k-2\ge k-1>1$. The penultimate definition then puts $a$ outside $N_G(u)\cup N_G(v)$. Every vertex of $T$ is at distance three from $w$ and is adjacent to $a$.

Fix a predecessor $p$ of $a$ on a shortest path from $w$ to $a$. It is distinct from $u,v$ because $a$ misses both endpoints. Let $c$ be the number of endpoints $u,v$ adjacent to $p$. Every vertex of $T$ is at distance exactly two from $p$ via $a$, using its distance three from $w$ for the lower bound. The other $2-c$ endpoint vertices are also at distance two from $p$ via $w$. Thus

$$
|T|\le k-2+c.
$$

On the other hand, count the union of the three closed even-distance sets as in the wedge proof. The vertices of $Q$ occur in both endpoint sets. The vertex $a$ lies outside $Q$ and belongs to the even-distance set of $w$, as well as the set of each endpoint adjacent to $p$ because $a$ misses both endpoints. It gives $c$ further duplicate incidences. Hence the union has at most $3(k+1)-|Q|-c$ vertices. The vertices outside the union are $C_1$ and $T$, and $|C_1|\le |Q|-1$ because $j_G=0$ and the common neighbor $w$ is outside $C_1$. Therefore

$$
|T|\ge n-3k-2+c.
$$

Combining gives $n\le4k$, contrary to the assumed order.

## A single degree increment at the hub

Write $t=\deg(h)-k$. Return to a longest path in $G$ starting at $z$, and let $u$ be an exterior vertex touching it. The [strict-degree contact bound](../root/rooted-local-ore.md) forces $h$ to be a mark of $u$, so $h$ is on the path. Since the successors are disjoint from $N(u)$ and are distinct from $z$, they all have degree exactly $k$. Every other mark has degree at most $k$ and therefore nonpositive wedge defect at $n>3k+2$. The rooted sum forces the hub wedge alone to have defect at least $|W|$.

Some exterior vertex has at least two marks. Otherwise every exterior component attaches to the path solely through $h$, contradicting 2-connectivity. Applying the exact wedge bound to the hub wedge with defect at least two yields

$$
n\le (t+2)k-k(k-e(h)).
$$

For $t=1$ this gives $n\le3k$, ruling out the open range and proving traceability.

Finally, the [moderate-order theorem](../root/moderate-order.md) covers $n\le4k+1$ at connectivity at least three if $k\ge13$. In the resulting connectivity-two case, a separating pair of ordinary degree-$k$ vertices is covered by the [exact-degree separating pair result](../sep/exact-degree-two-cut.md). A separating pair containing the sole below-$k$ vertex has wholly high components and is covered by the established all-high two-cut cases. Thus every separating pair in a remaining counterexample contains $h$.
