# Adjacent anchors with one and two misses

**Proposition.** Let a finite simple graph have vertex partition
$\{z,A,B\}\cup W\cup R$, where $W=\{p,q_1,q_2,c,d\}$ and
$|R|=6$. Suppose $N(z)=\{A,B\}$, the anchors $A,B$ are adjacent,
neither anchor sees $R$, and each vertex of $R$ has a neighbor in $W$.
Within $W$, anchor $A$ sees all vertices except $p$, and $B$ sees
exactly $p,c,d$. Suppose each vertex of $\{p,c,d\}\cup R$ has
degree at least five. Then some vertex of $\{A,B\}\cup W$ has at least
six vertices at distance exactly two.

Assume to the contrary that all seven of these distance-two sets have size
at most five. Call $c,d$ the common vertices. Write $P$ for the remotes
whose only neighbor in $W$ is $p$, and $Q$ for those whose nonempty
neighborhood in $W$ is contained in $\{q_1,q_2\}$. The sets are disjoint.
The distance-two set of $A$ contains $p$ and all remotes outside $P$,
so $|P|\ge2$. The corresponding set for $B$ contains both $q_i$
and all remotes outside $Q$, so $|Q|\ge3$. In particular at most one
remote lies outside $P\cup Q$. A remote with $k$ neighbors in $W$
misses at most $k$ of the other five remotes by its degree bound.

**Both common vertices meet a remote.** Suppose a common vertex, say $c$,
has no remote neighbor. Its degree gives at least three neighbors in $W$.
If it has all four possible neighbors there, then all six remotes are at
distance two. Thus $c$ misses exactly one other vertex $h$ of $W$.
Both $h$ and $z$ are at distance two from $c$ via the anchors. At most
three remotes can be at distance two, so at least three remotes must have
all their $W$-neighbors confined to $\{h\}$. In particular $h\ne d$,
since at most one remote lies outside $P\cup Q$.

If $h=p$, then $|P|\ge3$. Every vertex of $Q$ misses at most two
other remotes, so it meets $P$ and lies at distance two from $p$. The
vertices $z,A,c$ also lie at distance two from $p$ via $B$, giving
at least six. Thus $h$ is one of the $q_i$, say $q$. Let $T$ be
the at least three remotes whose only $W$-neighbor is $q$. Each vertex
of $T$ meets $P$, and each vertex of $P$ meets $T$, since each
misses at most one other remote. Now $z,A,T$ account for at least five
vertices at distance two from $p$, forcing $p$ to see both common
vertices, since any missed one is at distance two via $B$. Likewise
$z,B,P$ account for at least four vertices at distance two from $q$.
It must see at least one common vertex, since either missed common vertex
is at distance two via $A$. It misses $c$, so it sees $d$.
Then $d$ has $z$ and all of $P\cup T$ at distance two via the anchors,
$p$, and $q$, respectively, giving at least six. This proves the claim.

Consequently $R$ consists of the two vertices of $P$, three vertices of
$Q$, and a single vertex $s$ adjacent to both $c,d$. For a common
vertex $u$ with $t$ neighbors inside $W$, its distance-two set
contains $z$ and the $4-t$ missed vertices of $W\setminus\{u\}$
via the anchors. It therefore contains at most $t$ remotes. Moreover
$t\le3$, since if $t=4$ all five vertices of $P\cup Q$ are at
distance two, as is $z$.

Some $q_i$, say $q$, meets at least two vertices of $Q$, since
the two $q_i$ cover three vertices. Each vertex of $P$ meets at least one
of these two, since it misses at most one other remote. Thus $q$ has
$z,B$ and both vertices of $P$ at distance two, and must see at least
one common vertex $u$. This $u$ cannot see $p$, for then it would
have the two vertices of $P$ and the two neighbors of $q$ in $Q$
at distance two, exceeding its bound of three remotes.

It follows that $p$ misses a common vertex $u$. If $p$ saw $s$,
each vertex of $Q$ would meet at least one of the three remote neighbors
$P\cup\{s\}$ of $p$, since it misses at most two other remotes.
Then all three vertices of $Q$, together with $z,A,u$, would be at
distance two from $p$. Therefore $p$ misses $s$. Its only neighbors
outside $W$ are $B$ and the two vertices of $P$, so its degree forces
at least two neighbors in $W$. If it missed both common vertices, it
would see both $q_i$, putting all three vertices of $Q$ at distance two
besides $z,A,u$. Thus $p$ sees exactly one common vertex and at least
one $q_i$.

The distance-two set of $p$ now contains $z,A,u$, and $s$ via the other
common vertex. It contains at most one vertex of $Q$. Every member of $Q$
with a single $W$-neighbor misses at most one other remote and hence meets
$P$. Such a member lies at distance two from $p$, so at least two members
of $Q$ must see both $q_i$. But the $q_i$ adjacent to $p$ puts both
of them at distance two from $p$, the final contradiction.

This argument requires distance-two caps only at the anchors and in $W$.
Among vertices in $W$ it uses the degree bound only at $p,c,d$.
