# The bipartite case of the remaining Graph 199 child

Let \(G\) be a finite connected bipartite graph of vertex connectivity \(k\ge3\), with parts \(A,B\). Suppose its largest induced tree has at most \(k+2\) vertices and
\[
c(G-U)\le |U|+1
\]
for every \(U\subseteq V(G)\). Then \(G\) has a Hamiltonian path. Neither the connected-complement nor the independence-number condition of the current child is needed for this subcase.

The vertex connectivity gives \(d(v)\ge k\) for each vertex of \(G\). Since the graph is triangle-free, the center \(v\) and all its neighbors induce a star, so \(d(v)\le k+1\).

Two distinct vertices \(x,y\) with a common neighbor \(z\) belong to the same part. The path \(x,z,y\), together with every vertex of \(N(x)\triangle N(y)\) as a leaf on its unique adjacent endpoint, induces a tree. In particular
\[
|N(x)\triangle N(y)|\le k-1,\qquad
|N(x)\cap N(y)|\ge\frac{d(x)+d(y)-k+1}{2}.
\]
Thus if \(x\) and \(y\) have a common neighbor, then \(N(x)\) contains more than half of \(N(y)\). If two vertices each have a common neighbor with \(y\), their neighborhoods intersect inside \(N(y)\) by pigeonhole. It follows that the relation “equal or have a common neighbor” is transitive. Any walk of even length joins vertices related by this relation, by breaking it into length-two pieces. By connectedness, every two distinct vertices on the same side of the bipartition have a common neighbor and satisfy the displayed inequality.

Fix a side \(X\). If some \(x_0\in X\) has degree \(k\), then each other \(x\in X\) shares at least \((k+1)/2\) neighbors with \(x_0\). Each of the \(k\) vertices in \(N(x_0)\) accounts for at most \(k\) of these incidences because its total degree is at most \(k+1\). Thus
\[
(|X|-1)(k+1)\le2k^2.
\]
This is impossible for \(|X|\ge2k\), because \((2k-1)(k+1)=2k^2+k-1>2k^2\). Otherwise every vertex of \(X\) has degree \(k+1\). The same count gives
\[
(|X|-1)(k+3)\le2k(k+1),
\]
again impossible for \(|X|\ge2k\), because \((2k-1)(k+3)=2k(k+1)+3k-3\). In both cases \(|X|\le2k-1\). This holds on both sides.

Deleting one bipartition class leaves as many singleton components as there are vertices in the other. The separator assumption gives \(\bigl||A|-|B|\bigr|\le1\). If the parts have equal size \(r\), keep \(G\) as it is. If they differ by one, add a single new vertex to the smaller part and join it to the whole larger part, obtaining a balanced bipartite graph of part size \(r\). In both cases \(r\le2k-1\) and every cross-part nonedge has degree sum at least \(2k\ge r+1\).

For this balanced bipartite degree-sum criterion, adding any cross-part nonedge \(uv\) of degree sum at least \(r+1\) preserves the existence of a Hamiltonian cycle. If a Hamiltonian cycle after the addition uses \(uv\), delete that edge and write the resulting spanning path as \(u=x_1,y_1,x_2,y_2,\ldots,x_r,y_r=v\), with the \(x_i\) on one side. Some \(i\) satisfies both \(u\sim y_i\) and \(x_i\sim v\), by pigeonhole on the degree sum. Delete \(x_iy_i\) from the path and join its two pieces by those two edges. This gives a Hamiltonian cycle before the addition. Repeating until the graph is complete bipartite proves the criterion. If a new vertex was added, delete it from the cycle to get the required path in \(G\); otherwise delete any cycle edge.

## A further triangle-free restriction

The same argument implies that any triangle-free qualifying graph with no induced five-cycle is bipartite. Indeed for any \(x,y\) with a common neighbor \(z\), the two private sets \(N(x)\setminus N(y)\) and \(N(y)\setminus N(x)\) are independent within themselves by triangle-freeness. An edge between private vertices \(u,v\) would give an induced five-cycle \(x,u,v,y,z,x\). Consequently the induced double-star bound applies to all pairs with a common neighbor. The transitivity argument again works. No edge joins two members of one equivalence class since that would be a triangle. Fix a graph edge \(ab\); every vertex is related to \(a\) or \(b\) by taking an arbitrary walk from \(a\) and grouping its even-length portion into pairs of edges. These two equivalence classes form the desired bipartition.

One can also see directly that every triangle-free graph under the degree and tree bounds has diameter at most three. Otherwise take a geodesic \(x,u,v,w,y\) of length four. The vertices in \(N(x)\setminus N(v)\) and \(N(y)\setminus N(v)\) give independent leaf sets at the two endpoints. Within each set independence follows from triangle-freeness, between the sets any edge would shorten the geodesic, and none of the leaves meets any other path vertex by triangle-freeness or shortestness. There are at least \(d(x)+d(y)-d(v)\ge k-1\) such leaves, giving an induced tree of order at least \(k+4\).

This is a handwritten sufficient case for `WrittenOnTheWallII.GraphConjecture199.conjecture199.R1.H2.R1.H2`. It is independent of the earlier split-graph certificates. The separator condition is part of this child's input and is also separately proved for the conjecture's full tree-bound class by merged PR [#5650](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5650).
