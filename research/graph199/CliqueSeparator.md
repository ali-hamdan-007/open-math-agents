# Component bound for clique separators in WOWII #199

Let $G$ be a finite simple graph with vertex connectivity $k>0$ and no induced tree on more than $k+2$ vertices. If $U$ is a clique of size $m$, then $G-U$ has at most $m+1$ connected components.

Write $c$ for the number of components of $G-U$, and suppose $c\ge m+2$. For $u\in U$, let $R_u$ be the set of components containing a neighbor of $u$. For each component $C_j$, let $d_j$ count the vertices $u\in U$ for which $C_j\in R_u$.

- The neighbors of $C_j$ in $U$ form a vertex cut. Removing them separates $C_j$ from any other component of $G-U$, which still has all its vertices. Hence $k\le d_j\le m$.
- Choosing one neighbor of $u$ from each component in $R_u$ gives an induced star centered at $u$. Its leaves are in distinct components and have no edges between them. Hence $|R_u|\le k+1$.
- For distinct $u,v\in U$, choose one neighbor from each component in $R_u\mathbin{\triangle} R_v$, attached to the center that meets that component. The other center has no neighbor in the component. There are no edges between chosen leaves, and $uv$ is an edge because $U$ is a clique. The resulting induced double star has $2+|R_u\mathbin{\triangle}R_v|$ vertices. Hence $|R_u\mathbin{\triangle}R_v|\le k$.

Counting incidences gives $ck\le \sum_j d_j=\sum_{u\in U}|R_u|\le m(k+1)$. Since $c\ge m+2$, this forces $m\ge 2k$. In particular $km>0$.

Counting, by component, the unordered pairs of rows whose incidence differs gives
$$
\sum_{\{u,v\}\subseteq U}|R_u\mathbin{\triangle}R_v|
=\sum_j d_j(m-d_j)
\ge k\left(cm-\sum_j d_j\right)
\ge km(c-k-1).
$$
Each pair contributes at most $k$, so the same sum is at most $km(m-1)/2$. Canceling $km$ gives $2(c-k-1)\le m-1$. The assumption $c\ge m+2$ then forces $m\le 2k-3$, contradicting $m\ge 2k$.

The proof uses vertex connectivity only for an actual separating set with vertices on both sides. The empty clique is harmless because $k>0$ implies connectedness. If deletion leaves zero or one component, the bound holds immediately. The complete-graph convention for vertex connectivity therefore causes no exceptional case.

A Hamiltonian path implies the same component bound for every vertex set, by deleting vertices from the path. The argument above proves this necessary condition for clique separators from the induced-tree hypothesis itself.
