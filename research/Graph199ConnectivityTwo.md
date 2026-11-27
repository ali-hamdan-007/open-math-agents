# The two-component case of Written on the Wall II #199

Let $G$ be a finite simple graph with vertex connectivity two and largest induced tree of order at most four. Let $v,w$ be a two-vertex cut whose deletion leaves exactly two connected components $A,B$, with at least one nonclique. The reduction in `Graph199Noncliques.lean` already supplies a Hamiltonian path unless, after interchanging the components if necessary, $B$ is a clique, $A$ is a nonclique, and both $v,w$ are complete to $B$ and incomplete to $A$. The proof below closes this remaining case.

## The components beyond the neighborhood of $v$

Fix $b\in B$. Any induced four-vertex tree in $G[A\cup\{v\}]$ containing $v$ could be enlarged to a five-vertex induced tree by adding $b$, which is adjacent to $v$ and has no neighbors in $A$. This rules out every such four-vertex tree.

Set $S=N_G(v)\cap A$ and $T=A\setminus S$. Both sets are nonempty. Incompleteness gives a vertex of $T$, and connectivity after deleting $w$ forces $v$ to have a neighbor in $A$. Write $T_i$ for the connected components of $G[T]$.

Each $T_i$ has a neighbor in $S$ since $A$ is connected. If $a\in S$ has both a neighbor and a nonneighbor in $T_i$, connectivity gives an edge $xy$ of $T_i$ with $ax$ an edge and $ay$ absent. Then $v,a,x,y$ induce a forbidden four-vertex path. Thus each $a\in S$ is complete or anticomplete to $T_i$. A vertex $a$ complete to $T_i$ and two nonadjacent vertices of $T_i$ would form a forbidden claw centered at $a$, with $v$ as its third leaf. Therefore every $T_i$ is a clique. The same claw argument with one vertex in each of two different $T_i$ shows that no $a\in S$ can meet two of them.

Let $S_i\subseteq S$ be the nonempty set of vertices complete to $T_i$, and let $S_0$ be the vertices of $S$ anticomplete to $T$. For $a\in S_i$, $c\in S\setminus S_i$ and $x\in T_i$, if $ac$ were absent, then $x,a,v,c$ would induce a forbidden four-vertex path. Thus each $S_i$ is complete to all other groups, including $S_0$. Also, three pairwise nonadjacent vertices of $S$ would induce a forbidden claw with center $v$, so $\alpha(G[S])\le 2$.

## Traversing the groups

A nonempty induced subgraph of $G[S]$ is either connected and has a Hamiltonian path, or consists of two clique components. In the disconnected case, three components or a nonclique component paired with another component would give an independent triple. For the connected case, use the usual longest-path argument for independence number at most two. If a longest path misses $z$, both endpoints are nonadjacent to $z$. Its endpoints must then be adjacent, so the path closes to a cycle. Connectedness supplies an edge from outside the cycle to a cycle vertex. Enter at that vertex and traverse the cycle without closing it to obtain a longer path. The small graphs cause no exception because every connected graph on at least three vertices has a path on three vertices.

If $|S_i|\ge 2$, there is a path spanning $S_i\cup T_i$ with both endpoints in $S_i$. When $S_i$ is connected, insert a listing of the clique $T_i$ between two consecutive vertices of a Hamiltonian path of $G[S_i]$. When $S_i$ is disconnected, list its first clique component, then $T_i$, then its second clique component. Call either path a regular block.

If $S_i=\{a_i\}$, the block is dangling. In $G-a_i$, the only possible neighbors of $T_i$ outside $T_i$ lie at $w$. Since $G-a_i$ is connected, $w$ has a neighbor in $T_i$. There are at most two dangling blocks. Three would give three pairwise nonadjacent neighbors of $w$, one from each corresponding $T_i$, and $b$ would be a fourth independent neighbor. This is a forbidden induced five-vertex star.

## Combining the paths

If there are no dangling blocks, there is at least one regular block because $T$ is nonempty. If $S_0$ is nonempty and connected, begin with a Hamiltonian path of $G[S_0]$ followed by the regular blocks. If $S_0$ has two clique components, begin with the first clique, one regular block, and the second clique. Follow that with the remaining regular blocks. If $S_0$ is empty, use just the regular blocks. Each arrangement gives a spanning path of $A$ ending in $S$, and completes to a Hamiltonian path of $G$ by appending $v$, a listing of $B$, and $w$.

If a dangling block exists, label it $S_1\cup T_1$ with $S_1=\{a_1\}$. Begin by listing $T_1$, ending at a neighbor of $w$, then traverse $w$, all of $B$, and $v$. The remainder of the path starts with the following vertices.

- If $S_0$ is empty, take $a_1$.
- If $S_0$ is nonempty and connected, traverse its Hamiltonian path and then take $a_1$.
- If $S_0$ has two clique components, list the first, then take $a_1$, then list the second.

In every case the first vertex after $v$ is in $S$, and the last vertex of this segment is in $S_0\cup\{a_1\}$. Next traverse all regular blocks. If there is a second dangling block $S_2\cup T_2$, finish at $a_2$ and then along a listing of $T_2$. Every required join between distinct groups is an edge by the completeness proved above.

Both constructions visit each vertex exactly once. The graph may have the edge $vw$, but neither construction needs it. A clique used in any listing may consist of a single vertex.

## Small examples

Take $A=x-y-z$ and $B=\{b\}$, with both $v,w$ joined to $b$, and with no edges between $A$ and $B$.

- Let $v$ meet $x,z$, and $w$ meet $x,y$, with $vw$ absent. The block $x,y,z$ is regular even though $S_i=\{x,z\}$ is disconnected. The path $x,y,z,v,b,w$ spans the graph.
- Let $v$ meet $y,z$, and $w$ meet $x,y$, and add $vw$. Here $T_1=\{x\}$, $S_1=\{y\}$, and $S_0=\{z\}$. The path $x,w,b,v,z,y$ spans the graph.

Both examples have vertex connectivity two and largest induced tree of order four. Deleting any one vertex leaves them connected. Checking the six five-vertex induced subgraphs in each example rules out an induced tree of order five, which also rules out a larger induced tree by leaf deletion.
