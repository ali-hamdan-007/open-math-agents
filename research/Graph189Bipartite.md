# Bipartite case of WOWII 189

Let (G) be a connected bipartite graph with parts (X,Y), where (1le |X|le |Y|). Denote the second-smallest degree by (d_2). Assume every vertex has at most (1+d_2) vertices at even distance.

In a connected bipartite graph, the vertices at even distance from a vertex are exactly its part. Hence (d_2ge |Y|-1). At most one vertex has degree less than (d_2). If (|Y|ge2), at least one vertex in (Y) has degree at least (d_2), so (|X|ge |Y|-1).

If (|Y|=|X|+1), every vertex in (Y) except possibly one is adjacent to all of (X). Take the exceptional vertex first, if it exists, using an arbitrary neighbor given by connectivity. The rest of the vertices can be listed in alternating order, ending in (Y).

Suppose the parts both have size (m). For (m=1) the connected graph is an edge. For (m=2) the connected graph has at least three edges and is a spanning path or cycle. For (mge3), exchange the parts if necessary to place the exceptional vertex (x_*) in (X), or choose any (x_*in X) if there is no exception. In the graph (G-x_*), the missing cross edges form a matching: each remaining vertex had degree at least (m-1) in (G) and could be missing at most one original cross edge.

Write (k=m-1). Label the remaining vertices (x_0,ldots,x_{k-1}) and (y_0,ldots,y_k), extending the matching of missing edges so that its only possible pairs are (x_i y_i) for (0le i<k). For (kge3), the sequence
[
y_0,x_2,y_1,x_3,ldots,y_i,x_{i+2mod k},ldots,y_{k-1},x_1,y_k
]
is a Hamiltonian path of (G-x_*). Rotating indices gives one starting at any prescribed (y_i) for (i<k), and reversing gives one starting at (y_k). Thus choose its start adjacent to (x_*) and prepend (x_*).

For (k=2), if both possible missing edges are absent from (G-x_*), the path (y_0,x_1,y_2,x_0,y_1) spans (G-x_*). Both (y_0) and (y_1) have degree one there, so both are adjacent to (x_*) in (G), since all vertices of (Y) have degree at least (m-1=2). If at most one cross edge is missing, at least two vertices of (Y) are adjacent to both vertices of (Xsetminus{x_*}). Given the chosen starting neighbor of (x_*), use a different such vertex as the middle (Y)-vertex. Choose its two neighbors in order to accommodate the first and last (Y)-vertices. At most one of those two endpoints is missing an edge, so this always works.

Source for the full conjecture: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
