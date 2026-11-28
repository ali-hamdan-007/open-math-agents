# The order bound at a cut and the exterior of a universal completion

Write $n$ for the order, $s$ for vertex connectivity, $k$ for second-smallest degree, and $\delta$ for minimum degree. The even-distance cap is measured in the original graph.

## The cut-population order

Under the parent metric hypothesis, $2\le s\le k$ suffices for

$$
(n-2k-1)(k-s)\le sk^2.
$$

If the complete-graph convention applies, $n\le s+1$ and the left side is nonpositive. Otherwise take a minimum cut and any partition into two nonempty anticomplete sides. A singleton side gives $n\le(s+1)k+s+1$ by the existing separator cover. Consequently $n-2k-1\le sk$, which gives the claim directly. The proof works independently of the long-cycle lower order.

When both sides have size at least two, each contains a high vertex. If $X$ counts high vertices on one side, a high vertex and its neighbors occupy at most $X+s+1$ positions, since at most one vertex is low. Thus $X\ge k-s$ on both sides. Order the two populations as $X\le Y$. The verified inequalities $XY\le kX+sk^2$ and $n\le X+Y+s+1$ now give the result by Graph189CutPopulationOrder.population_order. [Graph-facing Lean source](../order/Graph189ActualPopulationOrder.lean)

## Independent exterior after deleting any vertex

Fix any $w$, let $H=G-w$, and let $P$ be a longest path of $H$. Suppose an originally high vertex $x$ outside $P$ is isolated in $H-P$. All $d_H(x)\ge k-1$ of its neighbors are path contacts. Their predecessors and the successor of the last contact give at least $d_H(x)+1$ distinct path vertices at distance two from $x$ in $H$. Each distance remains two in $G$. Hence $d_H(x)=k-1$, $xw$ is an edge, and the path already accounts for $k$ positive-even witnesses from $x$. Two such vertices $x,y$ would be at ambient distance two via $w$, which would exceed the cap.

In particular, if $H-P$ is independent, it has at most two vertices, at most one originally high and at most one originally low. This works for a removable vertex $w$ as well as for a minimum-degree vertex. In the other case write $D$ for a lower bound on all degrees in $H$, and suppose $d\ge2$ and $k+2d\le2D$. The cross-contact inequality and the exterior minimum-degree cycle construction supply a cycle of length at least $d+1$ in $H-P$. [Lean dichotomy](../lowblock/Graph189DeletionExterior.lean)

## Closing the at-most-two alternative at high minimum degree

Suppose $\delta\ge5$ and $2\delta>k$. If a longest path of $G$ misses at most three vertices, an omitted vertex $x$ has at most two omitted neighbors. For an omitted edge $xy$ with $x$ high, the exterior degree sum gives

$$
k+5\le d_G(x)+d_G(y)\le k+2|N(x)\setminus V(P)|\le k+4.
$$

An isolated omitted high vertex would have at least $k$ contacts and the strict single-contact shift would give at least $k+1$ positive-even witnesses. Hence all omitted vertices are low. If a vertex $z$ is omitted, it is the unique omission. Two of its contacts cannot be two positions apart on the path. Replacing their midpoint by $z$ produces another longest path omitting that originally high midpoint. Consequently the predecessors and successors of all $d_G(z)$ contacts are distinct distance-two witnesses, giving $2d_G(z)\le k$. This contradicts $2\delta>k$. Any path with at most three omissions therefore proves traceability in this regime. [Midpoint exchange](../verify/Graph189MidpointExchange.lean) and [three-omission gap](../lowblock/Graph189ThreeOmissionGap.lean)

In a nontraceable graph in this regime, the longest path in $G-w$ cannot have independent exterior, since it would give a path of $G$ with at most three omissions including $w$. The long exterior cycle therefore exists for every longest cycle of the graph obtained by making $w$ universal. The existing transfer opens that cycle at $w$. The cycle constructed off the corresponding path uses only original edges. This supplies the exterior hypothesis of the lifted-order proof without the earlier condition $4n<k(k-1)$ whenever the stated minimum-degree bounds hold. [Completion exterior](../lowblock/Graph189CompletionExterior.lean)

The graph-independent long-cycle theorem of Nikoghosyan is still required to convert the exterior conclusion into the scalar lower order. The range $2\delta\le k$ still uses the [all-order almost-spanning paper argument](../lowblock/all-near-spanning.md). [Nikoghosyan, Corollary A](https://noad.sci.am/Content/136032/03%20%281%29.pdf)
