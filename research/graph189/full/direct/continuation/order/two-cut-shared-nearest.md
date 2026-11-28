# Two deep components at a separating pair

Let $k$ be the second-smallest degree of a qualifying graph and let $S$ be a separating pair. The graph has vertex connectivity at least two. A port is a vertex of a side adjacent to a member of $S$. A high vertex has degree at least $k$. Each side is nonempty and no edge joins the sides.

## Both sides contain a high nonport with one nearest anchor

A pair of opposite high nonports has distance four. A shortest path crosses $S$ at distance two from each endpoint. In particular, if both vertices have a unique anchor at distance two, the two anchors coincide. Denote it by $i$.

Consider a high nonport $x$ on one side with sole nearest anchor $i$. Its two-edge path to $i$ has a predecessor adjacent to $i$ and to no other anchor. This predecessor sees every opposite $i$-contact at distance two. The separator boundary costs it one further even vertex. The opposite side therefore has at most $k-1$ such contacts. Every opposite high vertex missing $i$ is at even distance from $x$. Otherwise the two high vertices would have distance three, and crossing the separator on a shortest path would require a contact at the sole nearest anchor. The nonport spends two even vertices outside the opposite side, leaving at most $k-2$ high noncontacts. These bounds apply in both directions. [Sole-nearest budgets](Graph189SoleNearestData.lean)

An all-high side has size at most $2k-3$, internal minimum degree at least $k-2$, and at most $k-2$ vertices missing $i$. A Hamilton path in that side can be rotated and trimmed to start at an $i$-contact while losing at most one vertex. [Dense side routes](Graph189DenseSideRoute.lean)

If one side contains the low vertex $z$, erase it. The remaining region $R$ has internal minimum degree at least $d=k-3$, order at most $2k-3$ and at most $k-2$ noncontacts. Its high nonport from the hypothesis has $k$ neighbors in the original side, so $R$ has at least $k$ vertices and contains an $i$-contact. If $R$ is connected or has order at most $2d+1$, its longest path misses at most two vertices. Rotating and trimming to an $i$-contact costs at most two more. Including $z$, the side loses at most five.

In the other case, $R$ is disconnected and has more than $2d+1$ vertices. It contains at least three $i$-contacts. In the original connected side each vertex other than $z$ has degree at least $d+1$, and the order is at most $3d$. Split the components after deleting $z$ into two nonempty groups. Each group has at least $d+1$ vertices and minimum internal degree at least $d$, so both have order at most $2d-1$. Both induced graphs are Hamilton-connected by the prescribed-endpoint Ore bound. A group with at least two marked contacts can start at one distinct from a chosen neighbor of $z$. Joining through $z$ to a path spanning the other group gives a spanning side path beginning at a mark. [Marked articulation](Graph189MarkedLowCut.lean)

Join the two side paths through $i$. The losses on the two sides are at most five and one, and at most one anchor is missed. The ordinary path-omission theorem yields an original Hamilton path for $k\ge 26$. If a chosen side was disconnected already, deleting the separating pair gives at least three components, which the three-component theorem excludes in this range. [Two-cut assembly](Graph189SeparatedSideComponents.lean)

## Both deep sides have a common port

Assume each side contains a high nonport and a vertex adjacent to both anchors. Either common port sees all opposite ports at distance two. Each side therefore has at most $k$ ports. Each side has at most $k-2$ high nonports, by applying the separator debit to a high nonport in the other side, which sees them all at distance four.

If the first case does not apply, there is a side $A$ in which every high nonport is at distance two from both anchors. Write $r$ for their number. The two port sets, two inclusive even-distance sets at the anchors and the possible low vertex cover the graph. Every high nonport is counted at least once because it is at distance two from an anchor. Those in $A$ are counted twice. Hence $n+r\le 4k+3$. Counting the two sides separately gives $n\le 3k+r+1$. Together these yield $2n\le 7k+4$, so $n+5<4k$ for $k\ge 15$. The below-four-times-degree order theorem then furnishes an original Hamilton path. For $k\ge 26$ the first case supplies the other branch at every order. The two anchors may be adjacent or nonadjacent. [Both-common assembly](Graph189DeepCommonPair.lean)

## Adjacent anchors with a common-free side

Let $p,q$ be adjacent. At a vertex outside the even-distance sets of both anchors their distances are odd, and the triangle inequality forces them to be equal. Suppose $A$ has no common port. If its opposite side $B$ contains a high nonport, every high vertex of $A$ lies within distance two of an anchor. A high odd tie in $A$ would therefore be a common port, so $A$ contains at most one odd tie. The same conclusion follows when all high $A$ vertices are ports.

Choose a private $p$-contact in $A$, which exists by minimality of the separating pair. Its distance to every odd tie in $B$ is the common odd depth plus one. Indeed it can go through $p$ and every crossing path pays at least one step to an anchor. It also sees $q$ at distance two. Hence $B$ contains at most $k-1$ odd ties. Adding the two inclusive anchor budgets gives $n\le 3k+2$, and the checked moderate-order theorem supplies traceability at $k\ge 12$. Together with the both-common case this treats every adjacent separating pair with high nonports on both sides for $k\ge 26$. [Odd-tie order](Graph189AdjacentTieOrder.lean) and [original graph implication](Graph189AdjacentPrivateCut.lean)

The dense-side route, port rotation and ordinary omission input have passed the pinned Lean checker. The graph-to-order and final integration sources linked above are undergoing kernel replay.
