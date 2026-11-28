# A separating pair containing one vertex of degree k

Let $G$ satisfy Graph 189 with second-smallest degree $k$. If some separating pair of $G$ contains a vertex of degree $k$, then $G$ has a Hamiltonian path. The degree of the other separator vertex and the maximum degree of the graph are unrestricted. In particular, a counterexample with at most one vertex above $k$ cannot have connectivity two.

We use the previously settled cut-vertex, adjacent-pair, three-or-more-component, small-degree, and order-through-$3k+2$ cases. Thus suppose a counterexample is 2-connected, has order $n\ge3k+3$, and its separating pair is nonadjacent and leaves exactly two components. Write the pair as $\{p,h\}$ with $\deg(p)=k$, and the two components as $C,D$.

Call a vertex a port if it is adjacent to one of $p,h$, and common if it is adjacent to both. Every edge of a counterexample lies in a triangle by the [triangle-free edge cutoff](../root/edge-order.md). Each anchor consequently has at least two contacts in each side: it has a contact by 2-connectivity, and that edge needs a same-side triangle witness because the anchors are nonadjacent. In particular $p$ has at least one high contact on each side.

## Local Ore at the ordinary anchor

Choose high neighbors $u\in C$ and $v\in D$ of $p$. Each has degree at least $k$. The [local wedge inequality](../verify/wedge-order-and-hamiltonicity.md) gives $j_G(u,p,v)\le0$ because $n>3k+2$, $p$ has degree $k$ and its positive even-distance cap is $k$. Write $Q=N(p)\setminus(N(u)\cup N(v))$. The vertices $u,v$ both belong to $Q$, and the only possible common neighbors of $u,v$ are $p$ and $h$. Since $j_G=|Q|-|N(u)\cap N(v)|\le0$, equality is forced:

$$
Q=\{u,v\},\qquad N(u)\cap N(v)=\{p,h\}.
$$

The same wedge inequality would give $j_G<0$ if either endpoint had degree above $k$: its right-hand side would be at most $3k+2-n<0$. Hence, as $u,v$ were arbitrary high $p$-contacts, every high $p$-contact is common and has degree exactly $k$. Also every other $p$-contact in $C$ is adjacent to $u$, since it is not in $Q$ and cannot be adjacent to $v$ across the cut. Symmetrically $v$ sees all other $p$-contacts in $D$. The sets $N_C[u]$ and $N_D[v]$ each have size $k-1$, since $u,v$ each have degree $k$ and exactly two exterior neighbors. They all lie in the first two distance layers from $p$, as does $h$. These $2k-1$ vertices leave at most one further vertex in those layers, because $\deg(p)=k$ and its positive even-distance cap is $k$.

Each side has at most $k$ ports. All ports in one side are at distance two from a common port in the opposite side.

## Neither side is shallow

If either side consists entirely of ports, the [opposite-common-port bound](../sep/shallow-high-two-cut.md) gives $n\le3k+1$: that bound allows a low vertex on either side, and each side has a high common port. We may thus assume both sides have a nonport.

Suppose first that both sides have a high nonport. Every high nonport has distance exactly two from the pair $\{p,h\}$, since a high nonport on the opposite side is at distance at least four and the high-endpoint bound is four. If a high nonport is not at distance two from $h$, it must be at distance two from $p$ through the unique low vertex $z$, which must be a $p$-private port. Otherwise an intermediate $p$-contact is adjacent to $h$ and supplies the required distance two to $h$.

Such an exceptional high nonport lies outside $N_C[u]\cup N_D[v]$, because a neighbor of $u$ or $v$ is at distance two from $h$ unless it is adjacent to $h$, and a nonport is not. The near-saturation at $p$ permits at most one exceptional nonport. If such a vertex exists, $z$ itself is at distance two from $h$ via the high common $p$-contact in its side, which is adjacent to $z$ by the equality for $Q$. The cap at $h$ then counts $p$, $z$ and every other nonport, so at most $k-1$ nonports occur. If no exception occurs, $h$ counts $p$ and every high nonport, and there is at most one low nonport. Thus there are at most $k$ nonports in either case. With at most $k$ ports on each side this gives $n\le3k+2$.

Finally suppose one side, say $C$, has no high nonport. As it is not shallow, its sole nonport is the low vertex $z$. Every other vertex of $C$ is adjacent to $h$, since every high $p$-contact is common. Also $|C|\ge k-1$, since any high port in $C$ has at most two exterior neighbors.

If $|C|=k-1$, all high vertices of $C$ are internally universal and common in order to reach degree $k$. Fix one such high vertex $y$. For every $x\in D$, a path into $C$ passes through $\{p,h\}$, giving

$$
d_G(y,x)=1+d_G(x,\{p,h\}),\qquad
d_G(z,x)=2+d_G(x,\{p,h\}).
$$

The equalities follow because $y$ reaches each anchor in one step and $z$ reaches each in two. Exactly one distance is even. Both anchors are also at distance two from $z$, so the two caps imply $|D|\le2k-2$ and $n\le3k-1$.

If $|C|\ge k$, every nonport $x$ in the wholly high side $D$ has distance two from the pair. Otherwise its distance to all $|C|-1\ge k-1$ high ports of $C$ is at least four and hence exactly four. Its second layer also has at least two vertices by 2-connectivity: it separates $x$ from its nonempty fourth layer. This would exceed the cap. Since every $p$-contact is adjacent to $h$ when $z$ is a nonport, the high nonports in $D$ are all at distance two from $h$. So are $p$ and $z$, the latter via a neighbor in $C$. Therefore $h$ counts every nonport and $p$, leaving at most $k-1$ total nonports. The port counts again give $n\le3k+2$.

This proves the theorem for any pair containing a degree-$k$ vertex. In a counterexample a separating pair cannot contain the one possible below-$k$ vertex either: then both components are wholly high, which is covered by the [wholly high theorem](../sep/shallow-high-two-cut.md) and its cited companions. Consequently both separator vertices in any remaining counterexample must have degree above $k$. In particular this excludes connectivity two when at most one vertex has degree above $k$.
