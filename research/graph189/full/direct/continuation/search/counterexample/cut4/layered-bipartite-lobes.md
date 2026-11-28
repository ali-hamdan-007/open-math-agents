# Bipartite leaf blocks with two designated port banks

A rooted path obstruction gives nontraceable graphs of arbitrarily large connectivity with independently chosen integer leaf weights. The balanced examples can be exactly $1$-tough. None can satisfy Graph 189. The exclusion allows arbitrary pruning of leaf attachments and arbitrary external connections beyond the banks.

## Even-budget obstruction with sparse attachments

Let $k\ge11$ be the second-smallest degree in a qualifying graph. As usual, high vertices have degree at least $k$, there is at most one low vertex, and two high vertices have distance at most four.

Suppose a lobe has two disjoint banks $P_0,P_1$ with total size $R\ge8$ and $b\ge R-1$ pairwise disjoint nonempty bipartite leaf blocks. In block $j$, write $X_{j,0},X_{j,1}$ for its two nonempty parts. Each vertex in a part $X_{j,i}$ has no neighbors outside its own block except possibly vertices in its designated bank $P_i$. The allowed outside-neighbor sets may be arbitrary and possibly empty, even for vertices in the same part. The bank sizes, the graphs inside the blocks and on the banks, and the other neighbors of bank vertices are arbitrary. Under these assumptions the graph cannot qualify.

For a bank vertex $v$, all of its neighbors in leaf blocks lie in a single part per block. They are pairwise nonadjacent. Any one of these neighbors sees every other one at distance two via $v$. Thus a bank vertex has at most $k+1$ leaf neighbors. Counting bank-to-leaf incidences across all banks gives an upper bound of $R(k+1)$.

Call a high leaf vertex remote if it has no bank neighbor. Two remote vertices from different leaves are at distance at least four because a path leaving either leaf from its remote endpoint requires at least two edges before reaching a bank. The high-pair distance bound makes their distance exactly four. If any remote high vertex exists, discard its leaf block from the lower count. All remote high vertices in the remaining leaves are in its even quota, so there are at most $k$ of them. If none exists, discard an arbitrary leaf and the same bound holds.

Consider a leaf with parts of sizes $p,q$. A high vertex of the $p$-part with a bank neighbor has at least $\max(1,k-q)$ bank neighbors. A high remote vertex in that part can exist only when $q\ge k$, so in this case the removed term is exactly one. The other part is symmetric. If the low vertex is in this leaf, the term omitted for it is at most $k-1$, as the opposite part is nonempty. Consequently a leaf with $r$ remote high vertices pays at least
$$
p\max(1,k-q)+q\max(1,k-p)-r-(k-1)\mathbf 1_{\text{leaf contains the low vertex}}
$$
bank incidences. The first two terms sum to at least $2(k-1)$. To see this, truncating either part size above $k-1$ can only decrease that sum. On the square $1\le p,q\le k-1$ it is the bilinear expression $k(p+q)-2pq$, whose minimum is attained at a corner. Both diagonal corners give $2(k-1)$ and the other corners give $k^2-2k+2\ge2(k-1)$.

There are at least $R-2$ retained leaves. Their total incidence demand is at least
$$
2(R-2)(k-1)-k-(k-1)=(2R-6)k-2R+5.
$$
This exceeds $R(k+1)$ since their difference is $(R-6)k-3R+5$, at least three for $R\ge8,k\ge11$. No assumption about traceability or the size of the whole graph was needed.

## A nontraceable family at any connectivity $s\ge4$

Take at least three lobes with two banks of $s$ vertices each. Make each bank a clique and place a perfect matching between the two banks of each lobe. Connect lobes only through their $P_0$ banks, adding all cross edges between such banks whenever the lobe indices are adjacent in a connected simple core. In each lobe use $2s-1$ leaf blocks, each a complete bipartite graph $K_{p_j,q_j}$ with $p_j,q_j\ge s$. A part can attach only to its designated bank. Require each leaf to have at least $s$ pairwise vertex-disjoint attachment edges. This condition is also satisfied by complete joins to the designated banks.

Deletion of fewer than $s$ vertices leaves both banks in every lobe connected, their matching with a surviving edge, and every bipartite leaf connected. At least one of its disjoint attachment edges survives. The surviving $P_0$ banks remain connected along the core. Deleting just the $s$ vertices of any one $P_0$ bank isolates the rest of its lobe. Thus the graph has connectivity exactly $s$.

Choose $|p_j-q_j|\le1$ with an odd number of balanced leaves in each lobe. Suppose that there were a spanning path. Take a lobe containing neither global endpoint. The maximal path intervals inside this lobe must all enter and exit at $P_0$ vertices. If there are $t$ such intervals, there are $2s-t$ gaps between consecutive bank vertices within the intervals. Each of the $2s-1$ leaves must appear in a gap, and a gap can contain vertices of at most one leaf. Thus $t=1$ and every gap contains the whole of a distinct leaf, with no gaps available for a direct bank edge. In a spanning path of a balanced bipartite leaf the ends lie in opposite parts. In a leaf whose part sizes differ by one the ends both lie in the larger part. Therefore the bank layer changes exactly once for every balanced leaf and stays the same at every other leaf. An odd number of changes is incompatible with both ends lying in $P_0$. This certifies nontraceability for all the stated integer weights. A leaf whose part sizes differ by more than one instead makes its required spanning run impossible directly.

Taking all $p_j,q_j\ge\max(s,11)$ puts the family in the requested degree range. The leaf vertices already have degree at least eleven inside their own blocks. The banks can use the complete designated joins, which also give degree at least eleven at every bank vertex. More generally the sparse-attachment exclusion applies even if bank degrees are unrestricted.

## Exactly $1$-tough examples

Take all leaves balanced with independently chosen sizes, use the complete designated-bank joins, and make the lobe core complete so all $P_0$ vertices form one clique. For a vertex set $Z$, the surviving $P_0$ vertices form at most one central component. Write $Z_C$ for the deletions in a lobe $C$.

If both banks survive, the lobe has at most one component not meeting the central component, since every leaf vertex meets a surviving bank and each bank is a clique. Such a detached component requires the deletion of at least $s$ endpoints of the local vertical matching. If one bank is gone, components not meeting the other bank are surviving vertices of the removed bank's color in leaves whose opposite part was deleted in full. Balance charges each such isolated vertex to a distinct deleted opposite-part vertex. If the surviving bank itself forms a detached component, charge it to one of the $s$ deleted bank vertices. If both banks are gone, a leaf gives at most one component plus the number of deletions in it, since any one-color remainder has at most as many vertices as its deleted opposite part. There are $2s-1$ leaves and $2s$ deleted bank vertices.

In all cases a lobe with detached components contributes at most $|Z_C|-1$ such components. When the graph after deletion is disconnected, summing these bounds with the possible central component gives at most $|Z|$ components. Deleting both banks of a single lobe leaves its $2s-1$ leaf components and one central component from all the other lobes, attaining equality with $|Z|=2s$. Thus the graph has toughness exactly one and still has the rooted parity obstruction to a spanning path.
