# Stellated multipartite templates in Graph 189

The 14-vertex Goodey nontraceable triangulation is the octahedron with a vertex inserted in each of its eight triangular faces. Its eight new vertices are independent and can attach only to the six original vertices, certifying nontraceability. The original example and the triangle-identification constructions are discussed in [de Wet and Van Aardt, *Traceability of locally hamiltonian and locally traceable graphs*, Figures 1 and 13 and Theorems 3.10 and 3.14](https://dmtcs.episciences.org/articles/2144/download).

The following two results exclude all positive clique blow-ups of this base and extend to arbitrary irregular attachments in the specified families. The proofs use the actual second-smallest degree and graph distances. They do not need any order cutoff.

## A complementary-face count

Take a core with $m$ pairs of nonempty clique fibers $A_{i,0},A_{i,1}$. Edges between distinct pairs are complete, and opposite fibers of the same pair are anticomplete. For every binary face $f\in\{0,1\}^m$, take a nonempty lobe $C_f$ of arbitrary internal graph. Distinct lobes are anticomplete. Each vertex in $C_f$ may attach to any subset of the $m$ selected fibers $A_{i,f_i}$, with complete joins to the selected fibers. Assume it omits at most $r$ of these $m$ fibers.

If $m\ge\max(3,2r+2)$, **no graph in this family satisfies the Graph 189 hypotheses**, regardless of all fiber sizes, lobe orders, individual port masks, and lobe edges.

Write $A$ for the total core order, $\sigma(f)=\sum_i |A_{i,f_i}|$, and $W=\sum_f |C_f|$. Call a vertex high if its degree is at least the second-smallest degree $k$. At most one lobe can have no high vertex. In that case discard its face and the complementary face. Otherwise discard nothing. The set $F$ of retained faces is closed under complementation, and every $f\in F$ has a high representative $x_f\in C_f$.

Every core vertex in an opposite fiber $A_{i,1-f_i}$ is at distance two from $x_f$. Indeed it is nonadjacent to $x_f$, and $x_f$ has at least two selected ports in distinct pairs, so it has a common neighbor with that opposite vertex. The opposite fibers contribute $A-\sigma(f)$ witnesses.

If $g$ differs from $f$ in exactly one coordinate, the designated supports share $m-1$ fibers. Two vertices from those lobes omit at most $2r$ fibers between them, and $m-1>2r$. Thus they share a selected fiber, making their distance exactly two. Every such lobe contributes all its vertices as even-distance witnesses from $x_f$. The degree of $x_f$ is at most $|C_f|-1+\sigma(f)$. Combining its degree and even-distance bounds gives

$$
\sum_{g:\,d_{\mathrm{Ham}}(f,g)=1}|C_g|+(A-\sigma(f))
\le k\le |C_f|-1+\sigma(f).
$$

Sum over $f\in F$. The core terms cancel because $\sigma(f)+\sigma(\bar f)=A$. Any face $g$ has $m$ Hamming-distance-one neighbors, and at most one was discarded. Otherwise it would be a neighbor of two complementary faces, which are at distance $m\ge3$ from one another. Thus the sum of the lobe witnesses is at least $(m-1)W$, while the remaining upper bound is $\sum_{f\in F}(|C_f|-1)<W$. This is impossible.

For $m=3,r=0$ this already excludes every positive weighted clique blow-up of the original Goodey graph. For $r=1$ it excludes the arbitrary one-missing-port version in every dimension $m\ge4$, even with unrestricted lobe interiors.

## Irregular clique decorations of the octahedron

Take $m=3$ and $r=1$. Now assume each lobe is a clique and the union of its port masks contains all three of its designated fibers. Then every qualifying graph in this family has a spanning path. In particular this covers simultaneous triangle-identification decorations that add an arbitrary clique on a satellite vertex and two of its original face anchors, independently in each face, followed by arbitrary positive clique blow-ups.

If all six core fibers are singletons, a core vertex sees its opposite core vertex and every vertex in the four faces selecting that opposite at distance two. For the face vertices, their at least two selected ports ensure one in another pair, so the distance really is two. Applying the cap at the two opposite core vertices gives $W\le2(k-1)$.

At least seven lobes contain a high vertex. Any such lobe has order at least $\max(1,k-2)$, because an outside vertex has at most three core neighbors. The eighth lobe is nonempty, so $W\ge7\max(1,k-2)+1$. This strictly exceeds $2(k-1)$ for all positive $k$. Thus some core fiber has at least two vertices in a qualifying graph.

Label the three core pairs $a_0,a_1$, $b_0,b_1$, $c_0,c_1$. By symmetry the repeated fiber can be $a_0$. The following sequence visits all eight lobes, uses two vertices of $a_0$, and uses one vertex of each other core fiber:

$$
000,\ a_0,\ 001,\ c_1,\ 011,\ a_0,\ 010,\ c_0,\ 
100,\ b_0,\ 101,\ a_1,\ 110,\ b_1,\ 111.
$$

The two anchors on either side of an intermediate lobe are distinct and each belongs to its designated support. A singleton lobe is adjacent to them both by the full-support condition. For a lobe with at least two vertices, each of the two anchor fibers has a nonempty neighbor set, and their union is the whole lobe because every vertex uses at least two of the three ports. Thus they have distinct representative neighbors. Traverse the clique between those two representatives. An endpoint lobe can be traversed with any one representative as its assigned end. Extra core vertices can be inserted consecutively in a visit to their own clique fiber. This gives a spanning path in every case.

The argument only uses the complete joins from a chosen lobe vertex to its selected core fibers. Different vertices of a lobe may choose different port masks.
