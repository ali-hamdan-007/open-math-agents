# Direct spanning path in the adjacent one-miss layout

## The two parts and the connecting edge

**Path gluing.** Let $U$ and $V$ be nonempty disjoint vertex sets of a graph. Suppose a path covers $U$ with endpoint $u$, a path covers $V$ with endpoint $v$, and $uv$ is an edge. Orient the first path toward $u$, orient the second away from $v$, and concatenate their vertex lists. The joining edge supplies the sole new consecutive pair, and disjointness ensures that each vertex occurs once. This gives a path covering $U\cup V$.

In Lean, `List.IsChain.append` handles adjacency and `List.nodup_append` handles disjointness. The existing list-of-blocks version appears as `IndexedPath.flatten_block_chain` in `WrittenOnTheWallII.GraphConjecture189.conjecture189.R1.H1.R1.lean`.

## The eight-vertex part

**Two designated endpoints.** Let a graph have vertex set $\{z,a,b,p,q\}\sqcup C$, where $|C|=3$. Suppose $z$ sees both $a,b$, $b$ sees $p$ and all of $C$, and $a$ sees $q$ and all of $C$. Write $W=\{p,q\}\sqcup C$. If each $c\in C$ has at least two neighbors in $W$ and at least one of $p,q$ has a neighbor in $W$, then the graph has a spanning path with endpoint $p$, and one with endpoint $q$.

It suffices to construct the first path, since exchanging $p,q$ and $a,b$ gives the second.

- If $G[C]$ has at least two edges, choose a spanning path $c_1,c_2,c_3$ of $G[C]$. If $pq$ is an edge, use $p,q,a,z,b,c_1,c_2,c_3$. If $pq$ is absent, a spanning path of $G[C]$ can be chosen with $c_1$ adjacent to at least one of $p,q$. For a triangle, any vertex of $C$ can be its initial endpoint, and the positive $W$-degree assumption gives a suitable $c_1$. For a three-vertex path, its endpoints each need a second neighbor in $W$. If $pc_1$ is an edge, use $p,c_1,c_2,c_3,b,z,a,q$. If $qc_1$ is an edge, use $p,b,z,a,c_3,c_2,c_1,q$.
- If $G[C]$ has a sole edge $c_1c_2$, then $c_3$ sees both $p,q$. Use $p,c_3,q,a,z,b,c_1,c_2$.
- If $C$ is independent, all three vertices of $C$ see both $p,q$. Use $p,c_1,a,z,b,c_2,q,c_3$.

## The six-vertex part

**Four vertices of degree at least four.** A six-vertex graph of minimum degree at least two with at least four vertices of degree at least four has a spanning cycle. Consequently it has a spanning path with any prescribed endpoint.

Choose four vertices of degree at least four, forming a set $H$, and write $x,y$ for the other two. Every vertex in $H$ misses at most one other vertex. Thus $G[H]$ is $K_4$ minus a matching and $N_H(x)\cup N_H(y)=H$.

If $xy$ is absent, each of $x,y$ has at least two neighbors in $H$. Partition $H$ as $\{u,v\}\sqcup\{w,t\}$ with $u,v\in N_H(x)$ and $w,t\in N_H(y)$. To do so, extend $H\setminus N_H(y)$ to a two-element subset of $N_H(x)$ and take its complement. Between the two pairs the graph is $K_{2,2}$ minus a matching, so it retains at least one of the two perfect matchings. After exchanging $w,t$ if necessary, $uw,vt$ are edges, giving the cycle $x,u,w,y,t,v,x$.

Suppose $xy$ is an edge. Then $x$ and $y$ each have a neighbor in $H$.

- If $G[H]$ is complete, choose distinct $u\in N_H(x)$ and $v\in N_H(y)$. Such a choice exists since their union is $H$. Join $u$ and $v$ by an $H$-spanning path.
- If exactly one edge $uv$ of $H$ is missing, both $u,v$ see $x,y$, and $u,w,t,v$ is an $H$-spanning path, where $w,t$ are the other vertices.
- If two edges of $H$ are missing, each vertex of $H$ sees $x,y$, and $G[H]$ is a four-cycle. Delete one edge of the four-cycle and name its endpoints $u,v$. The other three edges form the required spanning path.

In all three cases add the edges $xu,vy,yx$ to the $H$-spanning path. To obtain a path with a prescribed endpoint in the resulting spanning cycle, delete an edge incident to that endpoint.

The same degree pattern gives a spanning cycle at every order $n\ge6$: minimum degree at least two and at most two vertices of degree less than $n-2$ suffice. For the inductive step designate two exceptional vertices, adding arbitrary vertices if there are fewer. Each exceptional vertex of degree two forbids deletion of at most two of the other $n-2\ge5$ vertices, so one of those vertices can be deleted while preserving the minimum degree and the degree threshold at order $n-1$. The deleted vertex has at most one nonneighbor in the graph, so extend the inductive cycle by inserting it along an edge avoiding that nonneighbor.

## Application to Graph 189

Assume order fourteen, and partition the vertices as $\{z,a,b\}\sqcup W\sqcup R$, with $|W|=5$ and $|R|=6$. The degree-two vertex $z$ has neighbors $a,b$, which are adjacent. Every vertex other than $z$ has degree at least five. Each vertex has at most five vertices at distance two. Neither anchor sees any of $R$, every vertex of $R$ sees some vertex of $W$, and $a$ sees every vertex in $W$ except $p$, while $b$ sees every vertex in $W$ except $q$, with $p\ne q$. Set $C=W\setminus\{p,q\}$ and
$$
P=\{r\in R:N_W(r)=\{p\}\},\qquad Q=\{r\in R:N_W(r)=\{q\}\},\qquad E=P\cup Q,\qquad S=R\setminus E.
$$

The anchor $a$ has $p$ and every vertex of $R\setminus P$ at distance two. Hence $|P|\ge2$, and the same argument at $b$ gives $|Q|\ge2$. Thus $|E|\ge4$, $|S|\le2$, and each $r\in E$ has at least four neighbors inside $R$.

**Degrees in $W$.** If $c\in C$ has at most one neighbor in $W$, it must see both vertices of $S$, since it sees both anchors and has no other possible neighbors. Each $r\in E$ sees at least one of those two vertices of $S$ because it misses at most one vertex of $R\setminus\{r\}$. Every vertex of $E$ is therefore at distance two from $c$, as is $z$. In addition, every nonneighbor of $c$ in $W\setminus\{c\}$ is at distance two through an anchor. This exceeds the cap of five, so each $c\in C$ has at least two neighbors in $W$.

If $p$ has no neighbor in $W$, it sees at least four vertices of $R$ by the degree bound. Each $r\in Q$ sees at least four vertices of $R$, so $N_R(p)$ and $N_R(r)$ intersect, as both are subsets of $R\setminus\{r\}$ of size at least four. Consequently all of $Q$ is at distance two from $p$. The same is true of $C\cup\{z\}$ through $b$, giving at least six vertices at distance two. Hence $p$ has a neighbor in $W$, and by symmetry so does $q$.

**Degrees in $R$.** Every $s\in S$ is at distance two from both anchors, by the definition of $S$ and its nonempty neighborhood in $W$. If $s$ has no neighbor in $R$, it sees all five vertices of $W$, so every other vertex of $R$ is at distance two from $s$ through $W$. Together with $a,b$ this exceeds five.

If $s\in S$ has exactly one neighbor $t\in R$, then each $r\in E\setminus\{t\}$ already misses $s$. Its degree inside $R$ forces it to see $t$, giving $a,b$ and all of $E\setminus\{t\}$ at distance two from $s$. The cap leaves only $|E|=4$ and $t\in E$. In this case let $s'$ be the second vertex of $S$. It cannot see $t$, and it cannot share a neighbor in $W$ with $s$, because either would give a sixth vertex at distance two from $s$. Since $s$ sees at least four vertices in $W$, $s'$ has at most one neighbor there. It also misses $s,t$, so it has at most three neighbors in $R$. This contradicts its degree of at least five. Therefore $G[R]$ has minimum degree at least two.

Apply the eight-vertex endpoint lemma to obtain a spanning path of $G[W\cup\{z,a,b\}]$ ending at $p$. Choose any $r\in P$, and apply the six-vertex lemma to get a spanning path of $G[R]$ starting at $r$. Glue them along $pr$ to give a spanning path of $G$.

This argument handles the surviving adjacent one-miss layout. The other four layouts require their respective exclusions. The proof uses the degree and distance-two bounds, without a Hall hypothesis or a closure theorem.
