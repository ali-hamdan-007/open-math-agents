# Two clique branches at each leaf of a layered construction

This family gives nontraceable graphs that can be exactly $1$-tough, have arbitrarily large vertex connectivity, and have every edge in a triangle. The obstruction survives arbitrary unequal positive clique sizes and sparse attachment patterns. At connectivity four the entire family is excluded from Graph 189 in the relevant $k\ge11$ range.

## Sparse-attachment exclusion

Let $s\ge4$. Consider one lobe with two banks $P_0,P_1$ of size $s$ each, and at least $2s-1$ disjoint leaf blocks. A leaf $L_j$ consists of ordinary branches $X_{j,0},X_{j,1}$, each of order at least two, and a singleton $z_j$. The vertex $z_j$ is adjacent to every ordinary vertex of its leaf. There are no edges between the two ordinary branches. The only possible neighbors of an ordinary vertex outside its own leaf lie in its designated bank. Such neighbors may be independently chosen for each vertex and can be absent. The articulation can have arbitrary neighbors in the two banks. Bank edges and the exterior network on the banks are arbitrary. Internal branch graphs need not be cliques for this exclusion.

Suppose the even-distance cap holds at the second-smallest degree $k\ge2s+3$. Every two high vertices, meaning vertices of degree at least $k$, have distance at most four. For any branch of order $w$, the opposite branch has all of its vertices at distance two from any vertex of the first, via $z_j$. Therefore both branch sizes are at most $k$. Every branch has a high vertex because it has at least two members. Its degree is at most $w+s$, allowing all same-branch vertices, the articulation and all $s$ bank vertices. So each branch has order between $k-s$ and $k$.

Call an ordinary high vertex remote when it has no bank neighbor. Two such vertices in different leaves have distance at least four, as each has no neighbor outside its own leaf and a path must leave both leaf blocks. Hence they are at distance exactly four. If there is a remote high vertex, discard its leaf from the count and observe that its even quota leaves at most $k$ remote highs in the retained leaves. Otherwise discard any one leaf. In either case at least $4s-4$ ordinary branches remain.

For a bank vertex touching ordinary vertices of at least two retained branches, these branches belong to different leaves since the bank is exclusive to one layer. Suppose its $t\ge2$ retained neighbor groups have sizes $m_1,\ldots,m_t$. A neighbor in group $i$ sees all its opposite branch at distance two, using at least $k-s$ even slots. At distance two through the bank vertex it also sees all $\sum_{j\ne i}m_j$ members of the other groups. Thus each of these sums is at most $s$, and
$$
(t-1)\sum_{j=1}^t m_j\le ts.
$$
The bank vertex has at most $2s$ ordinary neighbors in the retained leaves.

Let $e$ be the number of bank vertices with exactly one retained ordinary neighbor group. From the lower count discard any branch touched by one of those $e$ vertices, losing at most $e$ branches. The remaining branches contain at least $(4s-4-e)(k-s)-1$ high ordinary vertices, since at most one vertex is low. At most $k$ of these highs are remote. Every remaining ported high contributes at least one incidence at a bank vertex which originally had at least two retained groups. There are at most $2s-e$ such bank vertices. Consequently
$$
(4s-4-e)(k-s)-k-1\le2s(2s-e).
$$
At $k=2s+3$ the left side exceeds the right side by $6s-16+e(s-3)>0$. The difference increases with $k$ because its slope is $4s-5-e\ge2s-5>0$. This contradiction covers arbitrary integer branch sizes and arbitrary leaf attachment pruning. At $s=4$ the cutoff is $k=11$.

## A cross-bank join excludes all $k$

The preceding result has an all-degree version when each bank contains a vertex adjacent to every vertex of the other bank. Such a vertex is at exact distance two from every ordinary port of the opposite-layer branches, using any bank neighbor of that port. Thus at most $k$ ordinary vertices in each layer have a bank neighbor, over all leaves of the lobe. After discarding one leaf using the remote argument, at most another $k$ high ordinary vertices are remote, with at most one low vertex. Hence there are at most $3k+1$ ordinary vertices in the retained leaves.

The degree argument gives at least $\max(2,k-s)$ vertices per branch, even in this all-degree version. Thus there are at least $(4s-4)\max(2,k-s)$ ordinary vertices in the retained leaves. For $k\le s+2$ this lower bound is $8s-8>3s+7\ge3k+1$. At $k=s+3$ it equals $12s-12>3s+10=3k+1$, and subsequently increases faster than $3k+1$. This closes the complete-bank construction and all its arbitrary branch-attachment prunings at every $k$.

## Explicit nontraceable clique-weight constructions

Take at least three such lobes, exactly $2s-1$ leaves in each, and make both ordinary branches of every leaf cliques. Each branch has arbitrary integral order at least $2s+3$. Keep its articulation a singleton and give it no neighbors outside its leaf. Make the union of the two banks in a lobe a clique. Connect lobes only through their $P_0$ banks, adding all cross edges along an arbitrary connected lobe core. In each branch choose at least $s$ pairwise vertex-disjoint edges to its designated bank. The bank attachment rule also permits the complete joins used below.

Deleting fewer than $s$ vertices leaves the banks of every lobe connected and each surviving branch connected to its bank via an intact attachment edge. A surviving articulation joins at least one surviving branch. The $P_0$ banks remain connected along the lobe core. Deleting a whole $P_0$ bank isolates the rest of its lobe, so connectivity is exactly $s$. Every branch vertex has internal degree at least $2s+3$. Each bank vertex is used by at least one of the disjoint attachments of every corresponding branch, so its degree is at least $3s-1$. Thus the second-smallest degree is at least $2s+3$.

Suppose there were a spanning path and choose a lobe containing neither endpoint. Every maximal path interval within that lobe enters and exits through the $P_0$ bank. If there are $t$ intervals, the $2s$ bank vertices give $2s-t$ gaps between consecutive bank visits within the intervals. Each leaf needs a separate gap. Thus $t=1$ and all $2s-1$ gaps must each contain exactly one whole leaf. A spanning leaf path must use its articulation between its two ordinary branches, since deleting the articulation splits the leaf into the two nonempty branches. Its ends are therefore in different branches. Every gap switches the layer of its bank endpoints, and there are an odd number of gaps. Both ends cannot lie in $P_0$, a contradiction. The proof uses no bound on the clique sizes.

## Exactly $1$-tough examples with all edges in triangles

Use complete branch-to-bank joins and a complete lobe core, leaving the articulations without bank edges. Then every edge is in a triangle. In particular, the bank union in a lobe is a clique, leaf and articulation edges extend inside a branch, and cross-lobe edges extend via a second $P_0$ vertex in one of their lobes.

After deleting an arbitrary vertex set $Z$, the surviving $P_0$ vertices form at most one central component. For a lobe $C$, write $Z_C$ for its deleted vertices.

- If both banks survive, every surviving ordinary branch vertex reaches the central component. Only an isolated articulation can be detached. Such an articulation requires deletion of its entire two branches, so each detached component can be charged to at least two deletions.
- If one bank survives, each detached leaf piece requires a deletion in its leaf. Either its articulation was deleted, separating the ordinary branch whose bank is gone, or the whole branch of the surviving-bank color was deleted. In each case there is at most one detached piece per leaf, since both ordinary branches are cliques. The possible component containing the remaining bank can also be detached, and is paid for by the $s$ deletions of the other bank.
- If both banks are deleted, each of the $2s-1$ leaves forms at most one component plus one additional component if its articulation is deleted. This is at most $|Z_C|-1$ components in total.

A lobe with detached components in any case contributes at most $|Z_C|-1$ of them. If the deletion disconnects the graph, summing and allowing the one central component gives at most $|Z|$ components. Equality occurs after deleting both banks of one lobe, leaving its $2s-1$ connected leaves and one central component from the other lobes. The graph has toughness exactly one. Thus neither the triangle-free-edge filter nor the necessary path component bound can certify its nontraceability, while the rooted parity argument and the even-budget exclusion both apply.
