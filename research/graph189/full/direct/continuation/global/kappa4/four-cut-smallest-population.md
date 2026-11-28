# The smallest permitted high population on a four-cut

Assume a minimum four-cut has high anchors, both sides have a high vertex, and all high nonports have a nearest label at distance two. Suppose the small side has exactly $x=k-4$ high vertices and the larger side has $y$ high vertices with $2y>7k-2$. Then either the graph violates the even-distance condition or the cut has four common high labels and a high private large-side port at a label touching at least $k-3$ actual small-side vertices.

The degree bound forces the small side to contain the unique low vertex $z$ and all of its high vertices to be adjacent to every vertex of their side and every anchor. The larger side is wholly high. Put $L=N(z)\cap S$. Since $z$ has degree $k-4+|L|<k$, $m=4-|L|\ge1$. If $L$ is empty, every high large-side nonport is at distance exactly four from $z$, which also sees all four anchors at two. There are at most $k-4$ such nonports. Every large-side port is at distance two from any fixed high small-side vertex, so there are at most $k$ ports. Thus $y\le2k-4$, contradicting the order inequality.

If there is a private high large-side port at a label of $L$, then that label has $x+1=k-3$ actual opposite contacts and the stated conclusion holds. Otherwise every large-side port at a label of $L$ has at least two labels. A large-side nonport whose nearest-label mask misses $L$ has distance exactly four from $z$. This follows because all anchors outside $L$ are at distance two from $z$, and anchors in $L$ are at distance at least three from the nonport. The $m$ anchors missing $z$ are also at distance two from it. Thus at most $k-m$ high large-side nonports have a nearest-label mask avoiding $L$.

There are at least $y-k$ high large-side nonports, and every one meeting $L$ needs at least two nearest labels, by the support of its predecessor port. Their total anchor incidence count is at least
$$2(y-k)-(k-m)=2y-3k+m.$$
The $m$ anchors missing $z$ spend one of their even places at $z$, so the remaining anchor capacity is at most $4k-m$. This contradicts $2y>7k-2$ and $m\ge1$.
