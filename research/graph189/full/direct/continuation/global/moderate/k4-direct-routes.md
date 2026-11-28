# Direct paths for the degree-four terminal patterns

The moderate catalogue has 30 patterns of order at most 14. A separate enumeration for order 15 has 72 patterns. A graph with second-smallest degree four and the even-distance hypothesis has order at most 15 by the rooted order bound. The direct constructions below replace the completion stage of the paper computation in `root/small-degree-order-windows.md` for degree four. The bounds that produce the longest deletion path and the completeness of the exterior enumeration are dependencies. The route replays here use ordinary Python.

Let $z$ be a minimum-degree vertex, $P_0,\ldots,P_{p-1}$ a longest path after its deletion, and $E$ the exterior. The target in the completion check at order 15 is 12 vertices. Earlier orders require $n-3$. Assume every single-vertex deletion of the original graph is connected.

| Terminal family | Moderate | Order 15 | Path order |
| --- | ---: | ---: | --- |
| One path contact site for all of $E$ | 30 | 45 | At least $n-2$ in the moderate catalogue, at least $n-3$ at order 15 |
| Triangle at sites 3 and 7, with a forced edge to $z$ | 0 | 24 | 12 |
| Triangle with all exterior vertices at both sites | 0 | 1 | 12 |
| One exterior singleton and a $K_4$ | 0 | 2 | 13 |

### One site

Write $c=P_t$ for the sole contact site. The exterior is a triangle, four-cycle, diamond, or $K_4$. In the first three cases the tabulated exterior path starts at a neighbor of $c$ and ends at a degree-two exterior vertex with one path contact. Its ambient degree at least four forces an edge to $z$. The relevant orders of exterior labels are $(0,1,2)$, $(0,2,1,3)$, and $(0,2,3,1)$ in the moderate representation. For $K_4$, connectivity after deleting $c$ supplies an exterior neighbor of $z$. The $c$-neighbors and $z$-neighbors in this $K_4$ admit distinct choices. Otherwise both sets equal $\{x\}$ and deleting $x$ isolates $E-x$. The complete graph has a spanning path between the chosen neighbors.

After deleting $c$, some $P_j$ with $j\ne t$ must neighbor $z$, since all edges from $E$ to $P$ originally end at $c$. Traverse the opposite path arm from its endpoint to $c$, then the spanning exterior path to $z$, and then $P_j$. Of the two segments on the arm containing $P_j$, take the longer one starting there. If this arm has $r$ vertices, at most $\lfloor(r-1)/2\rfloor$ are omitted. The maximum $r$ is six in the 30 moderate rows, and seven in the 45 single-site order-15 rows.

### Two sites

Here $p=11$ and $E$ is a triangle. Each exterior vertex touches $P_3$ or $P_7$. If $z$ has an exterior neighbor, start at $z$, traverse the triangle in an order starting at that neighbor, and exit at a site seen by its last vertex. Either $P_3,\dots,P_{10}$ or $P_7,\dots,P_0$ adds eight vertices. In 24 rows, an exterior vertex contacts only one site, so its two internal neighbors and one contact force a fourth neighbor at $z$.

In the remaining row, all three triangle vertices meet both sites. Suppose $z$ misses $E$. Every exterior vertex sees $P_2,P_4,P_6,P_8$ at exact distance two. An edge of $z$ to $P_3$ or $P_7$ would give a fifth such vertex, so $z$ misses both marks. At order 15 the rooted bound $n\le1+\deg(z)+4+\lfloor25/4\rfloor$ gives $\deg(z)\ge4$. A $z$-neighbor at position $0$ or $4$ extends the eleven-vertex path

$$P_0,P_1,P_2,P_3,E_1,E_2,E_3,P_7,P_6,P_5,P_4.$$

Reflecting the indices gives the same construction for positions 6 and 10. Otherwise $z$ has at least four neighbors among positions $1,2,5,8,9$. Such a set contains $\{1,2\}$ or $\{8,9\}$. Insert $z$ between the consecutive neighbors on $P$.

### Four sites

In both rows $p=9$. An exterior singleton $x$ sees $P_3,P_5,P_7$, or their reflections. The remaining four exterior vertices form a $K_4$ and all meet $P_4$. Follow $P_0,P_1,P_2,P_3,x,P_7,P_6,P_5,P_4$, then all four clique vertices. Reflect in the other row. These paths have thirteen vertices.

### Reproduction

From this directory run `python audit-k4-direct.py` for the 30 moderate rows. It checks all 792 admissible combinations of the exterior neighborhood of $z$ and a noncentral contact $P_j$. Of these paths, 396 span the graph, 388 omit one vertex, and 8 omit two. It determines admissibility by testing single-vertex deletions of the maximal graph for each possible exterior neighborhood.

Run `python export-k4-order15.py` and `python audit-k4-order15.py` for order 15. The exporter copies the independent C++ degree-window enumerator into a temporary directory and emits each graph just before completion testing. The second script checks adjacencies, simplicity, and path order directly in each mandatory graph with only the specified actual $z$-edges added. Across the tested scenarios, 732 paths span the graph, 730 omit one vertex, 190 omit two, and 179 omit three.
