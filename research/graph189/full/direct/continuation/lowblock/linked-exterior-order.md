# Structural order from a linked exterior

Write $n$ for the order of the original graph, $k$ for its second-smallest
degree, $s$ for its vertex connectivity, and $\delta$ for its minimum degree.
The even-distance cap is always evaluated in the original graph.

## The order estimate

The official proof of the large-order Bondy theorem by @koolkao contains a
stronger intermediate result without an order threshold. In a graph $K$
of connectivity at least $\ell$, let $C$ be a longest cycle. Suppose a set
$D$ in a single exterior component has at least $\ell+1$ vertices and
every pair of its distinct vertices can be joined in $D$ by a path on at
least $\ell$ vertices. The upstream `linked_contra` contradicts
$n+\ell(\ell-1)\le(\ell+1)\delta(K)$. When $\ell\le\delta(K)$, this gives

$$
 n\ \ge\ (\ell+1)(\delta(K)-\ell+2)-1.
$$

An exterior cycle with at least $\max(\ell+1,2\ell-2)$ vertices supplies
such a set. For any two vertices, the longer arc contains at least $\ell$
vertices. A Hamilton-connected exterior set of order at least $\ell+1$
also qualifies. The graph-facing statements accept an actual exterior cycle
or an injective image of an induced Hamilton-connected set.
[Accepted upstream proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7971)
and [graph-facing Lean statements](Graph189BondyExterior.lean).

## Arbitrary removable vertex

Choose a vertex $w$ whose universal completion raises connectivity to at
least (s+1). Remove $w$ from a longest completion cycle to obtain a
longest path $P$ in the original deletion. Write $E$ for the graph
induced off $P$ in that deletion. Assume $k+6\le2\delta$. The checked
original path gap and independent exterior lemmas force an edge in $E$.
For each exterior edge $ab$, the cross-contact count gives

$$
 2(\delta-1)\le k+2d_E(a).
$$

In particular every nonisolated vertex of $E$ has at least two neighbors.
Choose the unique original low vertex if it lies in $E$, or any vertex of
$E$ otherwise. Removing it leaves an edge between originally high
vertices. Indeed, an endpoint distinct from the chosen vertex has at least
two neighbors before the removal.

For any edge in this remaining graph $F$, both endpoints have original
degree at least $k$. The same cross-contact count consequently gives
$2(k-1)\le k+2d_E(a)$. Removing one vertex costs at most one neighbor,
so every nonisolated vertex of $F$ has degree at least
$\lfloor(k-3)/2\rfloor$. Discarding isolates exposes a nonempty graph
with that minimum degree, embedded in the actual completion exterior.
Closing a longest path in it gives an exterior cycle of length at least
$\lfloor(k-1)/2\rfloor$.

For $s\ge2$, $k\ge4s+1$, and $k+2s+2\le2\delta$, that length is at least
$2s$. The order estimate at $\ell=s+1$ gives the lifted original order
$(s+2)(\delta-(s+1)+2)-1\le n$. The removable-vertex theorem supplies
$w$ independently of the location of the original low vertex.
[High exterior construction](Graph189ArbitraryHalfExterior.lean) and
[lifted order statement](Graph189CriticalBondyOrder.lean).
