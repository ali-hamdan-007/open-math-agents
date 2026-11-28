# One near-spanning path for all degree-four terminal rows

Write the ordered path as $P_0,\ldots,P_{p-1}$. Its exterior graph $E$ has order $b$, and $z$ is the vertex deleted from the original graph. In each of the 30 canonical terminal rows, the union of all exterior contact rows consists of one index $t$. Set $c=P_t$. Each of the two path segments on either side of $c$ has at most six vertices.

The whole terminal catalogue consists of the following exterior graphs. Exterior labels in the table start at zero. The routes start at a $c$-neighbor and end at a $z$-neighbor.

| Exterior graph | Exact exterior row masks | Contact rows | Spanning exterior route |
| --- | --- | --- | --- |
| Triangle | $[6,5,3]$ | Every vertex meets $c$ | $0,1,2$ |
| Four-cycle | $[12,12,3,3]$ | Every vertex meets $c$ | $0,2,1,3$ |
| Diamond | $[12,12,11,7]$ | Vertices 0 and 1 meet $c$, with 2 and 3 optional | $0,2,3,1$ |
| Complete graph on four vertices | $[14,13,11,7]$ | Any nonempty subset meets $c$ | Any specified distinct endpoints |

In the first three rows the listed route's endpoints have exterior degree two. Each endpoint has one path contact and is high in the original graph. Its deletion degree is three, so it necessarily meets $z$. Thus the listed orders give genuine paths from $c$ through all of $E$ to $z$.

For the complete graph on four exterior vertices, connectivity of $G-c$ gives an exterior neighbor of $z$. If there were no such neighbor, $E$ would have no edge to the rest of $G-c$. The nonempty sets of exterior neighbors of $c$ and of $z$ admit distinct choices. Otherwise they would both equal one singleton $\{x\}$, and deleting $x$ would disconnect $E-x$ from the rest of the original graph. A complete graph has a spanning path with any two distinct prescribed endpoints, giving the same $c$-to-$z$ path through $E$.

Connectivity of $G-c$ gives a path neighbor $P_j$ of $z$ with $j\ne t$. Otherwise there would be no edge between $E\cup\{z\}$ and the remaining path vertices. Start at the endpoint of $P$ on the side of $c$ opposite $P_j$, follow $P$ to $c$, traverse the exterior route to $z$, and continue from $z$ to $P_j$. Within the side containing $P_j$, take the longer path segment available from $P_j$. One direction continues to the outside endpoint, and the other stops at the vertex beside $c$.

If this side has $r$ vertices and $P_j$ is in position $i$ within it, counted from one, the two choices cover $i$ and $r-i+1$ vertices. The number omitted is at most $\min(i-1,r-i)\le\lfloor(r-1)/2\rfloor\le2$. The constructed path is simple because its two path portions lie on different sides of $c$, the exterior route is disjoint from $P$, and $z$ appears once. Its order is at least $n-2$, which contradicts the gap required in the degree-four moderate case.

This argument covers all 30 terminal rows, including all rows of path orders 9 and 10. It uses no information about chords of the deletion path. Run `PYTHONDONTWRITEBYTECODE=1 python audit_k4_short_terminal.py` to check the explicit path lists for every allowed exterior neighborhood of $z$ and every noncentral path contact of $z$ in the catalogue.

## Connection to the original graph

`Graph189DeletionOrders` already proves the numeric path and exterior bounds from the actual longest deletion path and global gap. The graph-to-layout declarations in `Graph189Contact{Layout,Splices,WalkLayout,Prefix}.lean` are staged for pinned Lean checking. The independent replay in `audit_k4_layout.py` gives the exact 30 keys from those necessary layout conditions. A pinned-kernel proof of this finite coverage remains pending.

At the terminal end, `Graph189SingleContactPath.detour` is the generic list construction. Its inputs are the two oriented path arms, the oriented exterior spanning path, the edges at the common contact and at $z$, and the bound six on the arm entered from $z$. It returns a simple graph path list with at most two omissions. The finite replay checked 792 admissible pairs of an exterior neighborhood of $z$ and a noncentral path site across the 30 keys.
