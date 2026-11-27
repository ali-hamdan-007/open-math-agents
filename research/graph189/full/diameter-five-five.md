# Diameter-five exclusion through minimum degree five

This is a handwritten continuation of [diameter-five-four.md](diameter-five-four.md) under the same hypotheses. The conclusion is that a graph in this diameter-five class has minimum degree at least six.

Use the notation $k,A,W,R,U,T,w,r,u,t,\sigma$ from the earlier proof. Suppose $k=5$. A remote vertex in $R$ is called a bridge here if it has a neighbor in $U$. There are at least two such vertices, since deleting a sole bridge would separate $x$ from $T$. A remote has no neighbors outside $W\cup R\cup U$ and at least one in $W$.

For an anchor $a$ let $D_a$ be its distance-two neighbors in $R$. Each $D_a$ is precisely the set of remotes having a $W$-neighbor seen by $a$, and the $D_a$ cover $R$. Each $D_a$ is nonempty since $a$ is distance four from every far vertex and any corresponding geodesic contains a distance-two remote. Write $h=\sigma-t$. All $t$ far vertices count in the positive even-distance limit at any anchor, so $|D_a|\le h$. If an anchor sees all of $W$, then $|D_a|=r$.

Since complete anchor-to-$W$ incidence is impossible, $w\ne\sigma-k$. The bounds $w\ge\sigma-k$ and $w+1\le t\le\sigma-2$ leave exactly three choices for $(w,t)$.

## $w=\sigma-4,\quad t=\sigma-3$

Here $u=4$ from $u+t-1\ge\sigma$ and $w+u\le\sigma$. Each far vertex sees all of $U$ by degree, and $h=3$. Each anchor can miss at most one possible neighbor because $k+w=\sigma+1$. A bridge is at distance two from every far vertex and hence from at most three anchors. At least two anchors miss every neighbor of that bridge in $W$, so the bridge has exactly one $W$-neighbor. Any vertex $p\in W$ supporting a bridge therefore sees at most three anchors. Its degree is at most $3+(w-1)+|N(p)\cap R|$, so it must see at least two remotes.

If $r\le3$, any nonbridge has degree at most $w+r-1\le\sigma-2$, so all remotes are bridges. Those bridges must have at least two distinct $W$-supports, since otherwise deleting the unique support separates $x$ from $T$. Each support needs at least two remotes, and the remotes have unique supports. Thus $r\ge4$, a contradiction.

Suppose $r>3$. No anchor can see all $W$. If two anchors were nonadjacent, they would spend their sole possible miss on each other and would both see all $W$. Thus the anchors form a clique, and each misses exactly one vertex of $W$, which is at distance two via another anchor. Hence $|D_a|\le2$ for each $a$.

If $p$ supports a bridge, any anchor seeing $p$ counts all of $N(p)\cap R$ in $D_a$, so $p$ sees exactly two remotes. Its degree bound then forces it to see exactly three anchors. If two different vertices $p,q$ support bridges, they each miss two anchors. The sets of missing anchors are disjoint because each anchor misses exactly one $W$-vertex. Therefore some anchor sees both $p,q$. Its distance-two cap forces $N(p)\cap R=N(q)\cap R$, since each set has size two. This contradicts the unique $W$-support of any bridge adjacent to $p$.

If there is only one bridge support $p$, take any remote outside its two remote neighbors. Every one of its $W$-neighbors must be missed by all three anchors seeing $p$, since those anchors already have both their allowed remote witnesses through $p$. Pick such a $W$-neighbor $q$. It sees at most two anchors, so its degree forces at least three remote neighbors. Any anchor seeing $q$ counts all three at distance two, a contradiction.

## $w=\sigma-4,\quad t=\sigma-2$

Here $h=2$ and $u\le4$. Each far vertex misses at most $u+t-1-\sigma\le1$ vertices of $U\cup T$ other than itself. A remote $v$ at distance two from at least three anchors must miss at least one far vertex at distance two because $3+t>\sigma$. That far vertex misses every $U$-neighbor of $v$, hence $v$ has at most one $U$-neighbor. Its degree is at most $w+r-1+1=\sigma-4+r$, forcing $r\ge4$.

If $r\ge3$, no anchor can see all $W$. Each anchor can miss at most one of its possible neighbors, and any nonadjacent anchor pair would see all $W$. Thus the anchors form a clique, each misses one $W$-vertex that counts at distance two, and each reaches at most one remote at distance two. The sum of the numbers of distance-two anchors over all the remotes is at most five. Every remote has at least one such anchor. If a remote had at least three, this sum would be at least $3+(r-1)$, forcing $r\le3$, incompatible with $r\ge4$ proved above. Thus every remote has at most two distance-two anchors.

If $r=2$, each remote needs at least three neighbors in $U$, since its other potential neighbors number at most $w+1=\sigma-3$. Each far vertex misses at most one $U$-vertex, so the far vertices are all at distance two from each remote. Again each remote has at most two distance-two anchors.

In either case any $W$-vertex with a remote neighbor is seen by at most two anchors, hence missed by at least three. Each anchor can miss at most one possible neighbor, so there is at most one $W$-vertex with a remote neighbor. This vertex separates $x$ from $T$, contradicting 2-connectivity.

## $w=\sigma-3,\quad t=\sigma-2$

Here $h=2$ and $u=3$. Every far vertex sees all of $U$ by degree. Each anchor can miss at most two possible neighbors because $k+w=\sigma+2$. Every bridge is at distance two from all far vertices and hence from at most two anchors.

Suppose $r\ge3$, so no anchor can see all $W$. If two anchors $a,b$ are nonadjacent, each has used one of its possible misses and therefore misses exactly one $W$-vertex. The mate anchor is at distance two via $x$, so each counts at most one remote at distance two. The missed $W$-vertex of $a$ could not be reached from $a$ at distance two, because there is also a nonempty $D_a$. Since $a$ sees every anchor other than $b$ and each $W$-vertex sees an anchor, the missed $W$-vertex is seen only by $b$. Likewise the sole missed $W$-vertex of $b$ is seen only by $a$; the two missed vertices are distinct. Each remote outside $D_a$ has only the sole missed $W$-vertex of $a$ as its support, so it belongs to $D_b$. It follows that $r=|D_a\cup D_b|\le2$, a contradiction. Thus $A$ is a clique. Every anchor misses at least one $W$-vertex and every such miss is at distance two. Because each anchor counts at least one remote, it therefore misses exactly one $W$-vertex and counts at most one remote. Every $W$-neighbor of a bridge is seen by at most two anchors, and hence missed by at least three. Since each of the five anchors misses exactly one $W$-vertex, at most one $W$-vertex is available to bridge remotes. At least two bridges share it, contradicting the one-remote cap at any anchor seeing it.

If $r=2$, 2-connectivity makes both remotes bridges. If a bridge had two $W$-neighbors, at least three anchors would miss both. Any such anchor must be adjacent to every other anchor by its two-miss degree bound. Thus it counts both missed $W$-vertices at distance two, through their anchors. Together with all far vertices this leaves no place for a remote witness, contrary to every $D_a$ being nonempty. So each bridge has only one neighbor in $W$. Its degree is at most $1+1+3=5<\sigma$, since $k<\sigma$. This last contradiction proves the exclusion.
