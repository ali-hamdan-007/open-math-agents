# The order bound at a cut and the exterior of a universal completion

Write $n$ for the order, $s$ for vertex connectivity, $k$ for second-smallest degree, and $\delta$ for minimum degree. The even-distance cap is measured in the original graph.

## The cut-population order

Under the parent metric hypothesis, $2\le s\le k$ suffices for

$$
(n-2k-1)(k-s)\le sk^2.
$$

If the complete-graph convention applies, $n\le s+1$ and the left side is nonpositive. Otherwise take a minimum cut and any partition into two nonempty anticomplete sides. A singleton side gives $n\le(s+1)k+s+1$ by the existing separator cover. Consequently $n-2k-1\le sk$, which gives the claim directly. The proof works independently of the long-cycle lower order.

When both sides have size at least two, each contains a high vertex. If $X$ counts high vertices on one side, a high vertex and its neighbors occupy at most $X+s+1$ positions, since at most one vertex is low. Thus $X\ge k-s$ on both sides. Order the two populations as $X\le Y$. The verified inequalities $XY\le kX+sk^2$ and $n\le X+Y+s+1$ give the inequality by Graph189CutPopulationOrder.population_order. The active graph-facing theorem verifies it on the arithmetic domain $s\ge 5$, $3s<k$ and $s<n-1$. [Graph-facing Lean source](../global/arity/final/Graph189GraphPopulation.lean)

## Independent exterior after deleting any vertex

Fix any $w$, let $H=G-w$, and let $P$ be a longest path of $H$. Suppose an originally high vertex $x$ outside $P$ is isolated in $H-P$. All $d_H(x)\ge k-1$ of its neighbors are path contacts. Their predecessors and the successor of the last contact give at least $d_H(x)+1$ distinct path vertices at distance two from $x$ in $H$. Each distance remains two in $G$. Hence $d_H(x)=k-1$, $xw$ is an edge, and the path already accounts for $k$ positive-even witnesses from $x$. Two such vertices $x,y$ would be at ambient distance two via $w$, which would exceed the cap.

In particular, if $H-P$ is independent, it has at most two vertices, at most one originally high and at most one originally low. This works for a removable vertex $w$ as well as for a minimum-degree vertex. In the other case write $D$ for a lower bound on all degrees in $H$, and suppose $d\ge2$ and $k+2d\le2D$. The cross-contact inequality and the exterior minimum-degree cycle construction supply a cycle of length at least $d+1$ in $H-P$. [Independent exterior](../lowblock/Graph189IndependentExterior.lean) and [cycle from cross-contact counts](../lowblock/Graph189ExteriorPopulation.lean)

## Closing the at-most-two alternative at high minimum degree

Suppose $\delta\ge5$ and $2\delta>k$. If a longest path of $G$ misses at most three vertices, an omitted vertex $x$ has at most two omitted neighbors. For an omitted edge $xy$ with $x$ high, the exterior degree sum gives

$$
k+5\le d_G(x)+d_G(y)\le k+2|N(x)\setminus V(P)|\le k+4.
$$

An isolated omitted high vertex would have at least $k$ contacts and the strict single-contact shift would give at least $k+1$ positive-even witnesses. Hence all omitted vertices are low. If a vertex $z$ is omitted, it is the unique omission. Two of its contacts cannot be two positions apart on the path. Replacing their midpoint by $z$ produces another longest path omitting that originally high midpoint. Consequently the predecessors and successors of all $d_G(z)$ contacts are distinct distance-two witnesses, giving $2d_G(z)\le k$. This contradicts $2\delta>k$. Any path with at most three omissions therefore proves traceability in this regime. [Midpoint exchange](../verify/Graph189UniqueOmissionExchange.lean) and [three-omission gap](../lowblock/Graph189HighMinimumGap.lean)

In a nontraceable graph in this regime, the longest path in $G-w$ cannot have independent exterior, since it would give a path of $G$ with at most three omissions including $w$. The long exterior cycle therefore exists for every longest cycle of the graph obtained by making $w$ universal. The existing transfer opens that cycle at $w$. The cycle constructed off the corresponding path uses only original edges. This supplies the exterior hypothesis of the lifted-order proof without the earlier condition $4n<k(k-1)$ whenever the stated minimum-degree bounds hold. [Completion exterior](../lowblock/Graph189CriticalExterior.lean)

For a longest cycle with a residual cycle of length at least $\max(\ell+1,2\ell-2)$, the linked-set theorem from the accepted Bondy proof gives the scalar order at connectivity $\ell$. A minimum-degree vertex whose deletion is nontraceable supplies a residual cycle of length at least $\lceil k/2\rceil$. This satisfies both size requirements for $\ell\ge3$ and $4\ell-5\le k$. [Bondy linked-set source](../lowblock/Graph189BondyExterior.lean) and [minimum-deletion exterior](../lowblock/Graph189MinimumOrderViaCycles.lean)

## A shorter order calculation in the low-degree near-spanning branch

Suppose $G$ is nontraceable with $\delta\ge5$, $2\delta\le k$, and a path missing at most three vertices. The isolated-vertex and omitted-edge arguments above put every omitted vertex of an ordinary longest path below $k$. There is exactly one omitted vertex $z$, of degree $\delta$.

Let $Q$ be a longest path through $z$ and write $m$ for its number of omitted vertices. On the ordinary path spanning $G-z$, all $\delta$ neighbors of $z$ appear. Between their successive positions, or at an outer tail, replace the open interval by $z$. The resulting path through $z$ omits precisely the vertices of the replaced interval. Thus each of the $\delta+1$ intervals contains at least $m$ vertices, giving $n\ge1+\delta+(\delta+1)m$.

Assume the desired base bound fails. Since $s\le\delta$, the last inequality and $n<(s+1)(k-s+2)-1$ imply $m\le k-s$. Every vertex off $Q$ is high. If such a vertex were isolated off $Q$, all of its neighbors would be contacts on $Q$, and their distinct predecessors together with the last successor would overrun the distance-two budget. For an omitted edge, the two endpoint contact populations still produce distance-two witnesses. Two shifted indices can coincide only at the position of $z$, since a detour replacing any other single path vertex would retain $z$. This costs at most one witness, forcing internal degree at least $\lfloor k/2\rfloor$ throughout the omitted graph. As $m\le k-s$ and $s\ge 3$, the degree-sum closure theorem gives a Hamilton path in that graph between any distinct prescribed endpoints. [Protected contact and degree bounds](../lowblock/Graph189ProtectedExteriorDegree.lean) and [Hamilton-connected exterior](../lowblock/Graph189ProtectedHamiltonConnected.lean)

Put $u=k+1-m$. The positive internal minimum degree gives $m\ge\lfloor k/2\rfloor+1$, hence $s\le u\le m$ and $s\le m$. Choose $u$ distinct exterior vertices. Each has at least $u$ neighbors on $Q$, so they have distinct path contacts by greedy choice. Along $Q$, the $u$ chosen contacts bound $u+1$ disjoint open gaps and tails. At least $u$ avoid $z$. Each can be replaced by a spanning path of the omitted graph with the appropriate endpoint or endpoints, so each has at least $m$ vertices by maximality of $Q$. It follows that $n\ge m+u+mu$. The inequality $(m-s)(u-s)\ge0$ and $m+u=k+1$ imply $n\ge k+1+s(k+1-s)=(s+1)(k-s+2)-1$, as required. This direct base-order argument uses neither the classification of the omitted graph as a clique nor an exchange of two entire intervals. [Contact-gap upper bound](../lowblock/Graph189ProtectedExteriorSize.lean), [protected matching](../lowblock/Graph189ProtectedMatching.lean) and [traceable-deletion order](../lowblock/Graph189TraceableDeletionOrder.lean)


The graph-to-order implication above now passes the pinned Lean kernel. If deleting a vertex of degree strictly below the second-smallest degree leaves a Hamiltonian path and the full graph is nontraceable, then every integer index $3\le j\le\deg(z)$ with $2j\le k$ satisfies $(j+1)(k-j+2)\le n+1$. Taking $j=s$ supplies the baseline. Taking $j=s+1$ supplies the stronger lifted order whenever the minimum degree exceeds $s$ and the index fits the degree range. [Lean theorem](../lowblock/Graph189TraceableDeletionOrder.lean) · [Kernel audit](../lowblock/traceable-deletion-order.log)
