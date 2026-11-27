# Degree-two outer-layer bound and order-fourteen audit

The proofs below are handwritten. The Lean source `Graph189Order14Layout.lean` is the input for the order-fourteen split. The strengthened outer-layer bound and these counting eliminations have not been checked in Lean here.

## Outer-layer bound

Let $G$ be a finite simple graph and let $z$ have exactly two neighbors $a,b$. Suppose every vertex is within distance three of $z$. Let $W$ and $R$ be the sets at distance two and three from $z$, respectively. Let $s\ge 4$. Suppose every vertex other than $z$ has degree at least $s$ and every vertex has at most $s$ vertices at distance exactly two. Then
$$
|R|\le 2s-4.
$$

Write $w=|W|$ and $r=|R|$. The distance-two cap at $z$ gives $w\le s$. Every vertex of $W$ sees at least one anchor $a,b$, every vertex of $R$ sees at least one vertex of $W$, and no vertex of $R$ sees an anchor or $z$. Put
$$
D_a=\{u\in R:\operatorname{dist}(a,u)=2\},\qquad
D_b=\{u\in R:\operatorname{dist}(b,u)=2\}.
$$
A remote vertex lies in $D_a$ exactly when it has a neighbor in $W$ that sees $a$. The analogous statement holds for $b$. In particular $D_a\cup D_b=R$.

Assume $r\ge 2s-3$. Since $s\ge 4$, we have $r>s$. Each anchor must miss some vertex of $W$, since an anchor that saw all of $W$ would have all $r$ remote vertices at distance two. The sets missed by the anchors are disjoint, since each vertex of $W$ sees an anchor. If each anchor misses exactly one vertex, label the vertices seen only by $a$ and only by $b$ as $p$ and $q$, respectively. In these one-miss cases write $A=R\setminus D_b$ and $B=R\setminus D_a$. The sets $A,B$ are disjoint. Every vertex in $A$ has $p$ as its unique neighbor outside $R$, and every vertex in $B$ has $q$ as its unique neighbor outside $R$.

In either anchor configuration with one miss each, $|D_a|,|D_b|\le s-1$. If the anchors are adjacent, the missed middle vertex is at distance two through the opposite anchor. If they are nonadjacent, the opposite anchor is at distance two through $z$. Consequently
$$
|A|,|B|\ge r-s+1\ge s-2.
$$
Every vertex of $B$ has at least $s-1$ neighbors in $R$. It has at most $|D_b|-1\le s-2$ possible neighbors in $R\setminus A$, because it belongs to $D_b$. So it has a neighbor in $A$, and hence is at distance exactly two from $p$. The same argument puts every vertex of $A$ at distance exactly two from $q$.

### Adjacent anchors with one miss each

The degree of each anchor is $2+(w-1)=w+1$, so $w\ge s-1\ge 3$. A shared middle vertex $c\in W\setminus \{p,q\}$ therefore exists. At $p$, the vertices $z,b$ are at distance two through $a$, and the vertices of $B$ are at distance two by the preceding count. These exhaust the cap of $s$, since $|B|\ge s-2$. Every shared middle vertex that $p$ missed would also be at distance two through $a$. Thus $p$ sees every shared middle vertex. By symmetry so does $q$.

A shared middle vertex $c$ has no neighbor in $A\cup B$ by the unique outside-neighbor conditions. Through $p$ and $q$ it reaches all of $A\cup B$ at distance two. It also reaches $z$ at distance two through either anchor. Thus it has at least $2(s-2)+1=2s-3>s$ vertices at distance two, a contradiction. This last count uses $z$ to include $s=4$.

### Adjacent anchors with more than two total misses

Let $m_a,m_b$ be the numbers of vertices of $W$ missed by $a,b$. Each missed vertex is at distance two from the anchor that misses it, through the other anchor. Hence
$$
r\le |D_a|+|D_b|\le 2s-m_a-m_b.
$$
Because $m_a,m_b\ge 1$ and $r\ge 2s-3$, the only case left is $m_a+m_b=3$. Exchange the anchors if needed so that $m_a=1$ and $m_b=2$. Then all inequalities in the display are equalities. In particular $r=2s-3$, $|D_a|=s-1$, $|D_b|=s-2$, and these two sets partition $R$. The degree of $b$ is $2+(w-2)=w$, so the degree lower bound and $w\le s$ give $w=s$.

Let $v$ be the middle vertex seen only by $b$, and $x_1,x_2$ those seen only by $a$. The remaining $s-3\ge 1$ middle vertices see both anchors. The partition of $R$ means every vertex of $D_b$ sees $v$ as its sole middle neighbor, and every vertex of $D_a$ sees at least one of $x_1,x_2$ and has no other middle neighbors. A shared vertex $c$ has no remote neighbor. Since it has degree at least $s$ and exactly two anchor neighbors, it misses at most one other middle vertex.

If $c$ saw both $x_1,x_2$, all $s-1$ vertices of $D_a$ and $z$ would be at distance two from $c$. If $c$ missed $v$, then $v$ would also be at distance two through $b$. If $c$ saw $v$, then every vertex of the nonempty set $D_b$ would be at distance two via $v$. So $c$ must miss one of $x_1,x_2$, say $x_2$, and sees both $x_1$ and $v$.

The $s-2$ vertices of $D_b$, along with $z$ and $x_2$, fill the distance-two cap at $c$, via $v$ and $a$. Therefore $x_1$ has no neighbor in $D_a$, since such a neighbor would also be at distance two from $c$. It has no neighbor in $D_b$ by the partition. The only possible neighbors of $x_1$ are $a$ and the $s-1$ other middle vertices. Its degree forces every one of those edges. Every remote has some middle neighbor other than $x_1$, and thus is at distance exactly two from $x_1$. This contradicts $r>s$. For $s=4$ there is one shared vertex and $|D_a|=3, |D_b|=2$, so all counts still apply.

### Nonadjacent anchors

An anchor has one neighbor outside $W$, namely $z$, and misses at least one vertex in $W$. Its degree is thus at most $1+(w-1)=w\le s$. The degree lower bound forces equality, $w=s$, and one miss each. Use $p,q,A,B$ and their cross-layer distance-two properties from the beginning of the proof. There are $s-2$ shared middle vertices.

If $p$ had no shared middle neighbor, all $s-2$ shared middle vertices and $z$ would be at distance two from $p$ via $a$. Also $|B|\ge s-2$ remote vertices are at distance two from $p$. This is at least $2s-3>s$ vertices. Therefore $p$ has a shared middle neighbor, putting $p$ at distance exactly two from $b$. By symmetry $q$ is at distance exactly two from $a$. Each anchor now uses two places of its distance-two cap outside $R$, one for the opposite anchor and one for the unique middle vertex it misses. Thus $|D_a|,|D_b|\le s-2$ and $r\le 2s-4$, a contradiction.

## Order-fourteen audit

With the hypotheses of `Graph189Order14Layout.shapes`, write $s=5$. The connectedness and diameter bound partition the vertices into $\{z,a,b\},W,R$. The distance-two cap follows from the given even-distance cap because in diameter at most three the even-distance vertices are the vertex itself and its distance-two layer. Since $z$ has degree two, the second-smallest degree assumption implies that all other vertices have degree at least five.

- **Adjacent one miss each, $w=4$.** The layer partition gives $r=7$. The original proposed counting proof is valid, and the sharpened proof above excludes $r>6$. In the proposed proof every member of $B$ is in $D_b$, so subtracting itself from its possible neighbors in $D_b$ is justified.
- **Nonadjacent one miss each, $w=5$.** Here $r=6$. In the notation above the pure classes $A,B$ first have size at least two and are at distance two from $q,p$, respectively. The argument for the nonadjacent anchors makes the missing vertex and the opposite anchor distinct distance-two witnesses outside $R$ for each anchor. Thus $|D_a|,|D_b|\le 3$, and $|A|,|B|\ge 3$. They partition $R$ into two triples. The cap at $p$ is exhausted by $B,z,b$; any missing shared middle vertex adds a witness through $a$. Similarly $q$ sees every shared middle vertex. A shared middle vertex then sees all six remote vertices at distance two via $p$ or $q$. This verifies the proposed nonadjacent proof, including the step specific to $r=6$.
- **Adjacent two misses each, $w=5$.** Here $r=6$. The two misses per anchor give $|D_a|,|D_b|\le 3$; these sets partition $R$ into two triples. Let $X,Y$ be the $a$-private and $b$-private middle pairs, and $c$ the sole shared vertex. Each remote sees only the corresponding private pair in $W$, with at least one neighbor there. The vertex $c$ has no remote neighbor and sees at least three private vertices by degree. Seeing all four would put all six remotes at distance two from $c$. If $c$ misses $x\in X$ and sees $x'\in X$ and both vertices of $Y$, the witnesses $z,x,D_b$ exhaust its cap. Thus $x'$ has no neighbor in $D_a$ or $D_b$. Its degree forces adjacency to all four other middle vertices as well as $a$. Every remote then lies at distance two from $x'$, a contradiction. This verifies the proposed adjacent two-miss proof without using edges inside $R$.
- **Adjacent one and two misses, $w=5$.** The outer-layer bound does not exclude $r=6$ on its own. The mixed case in the proof above uses $r=2s-3$, which would be seven here. The separate order-fourteen argument is audited below.
- **Adjacent one miss each, $w=5$.** The bound permits $r=6$. A direct check of the recorded satisfying graph in `search_189_order14.txt` verifies that it attains the bound at $s=5$, so no stricter uniform bound is possible at this $s$.

## Audit of the remaining two order-fourteen cases

The counting argument in `adjacent-hand/proof.md` excludes the case of adjacent anchors with one and two misses at $r=6$. For the notation of that write-up, its anchor counts yield disjoint classes $P,Q$ with at least two and three remotes, respectively. If a common middle vertex has no remote neighbor, its degree and distance-two cap force at least three remotes supported only by the single middle vertex it misses. That middle vertex cannot be the other common vertex, because at most one remote lies outside $P\cup Q$. If the missed middle vertex is $p$, every one of the at least three vertices of $Q$ sees a vertex of $P$, giving six distance-two witnesses at $p$. If the missed middle vertex is one of the $q_i$, the remote cross edges force $p$ to see both common vertices and that $q_i$ to see the other common vertex. The latter common vertex then has at least six distance-two witnesses.

Once both common vertices have a remote neighbor, there is exactly one remote $s$ outside $P\cup Q$, with $|P|=2$ and $|Q|=3$. The $t$ middle neighbors of a common vertex allow it at most $t$ distance-two remotes, and $t\le3$, since $t=4$ would expose every member of $P\cup Q$ as well as $z$. Some $q_i$ sees two members of $Q$, placing both members of $P$ at distance two. Its own cap forces it to see some common vertex $u$. If $u$ also saw $p$, it would expose two remotes from each pure class and violate its cap. Thus $p$ misses $u$, and its own cap then also forces it to miss $s$. Its degree forces at least two middle neighbors, and it cannot miss both common vertices because then it would see both $q_i$, exposing all of $Q$ at distance two. The resulting four distance-two witnesses $z,A,u,s$ at $p$ leave room for at most one member of $Q$. Every single-support member of $Q$ sees some member of $P$ and already occupies such a place. At least two members of $Q$ therefore see both $q_i$, and both are exposed at distance two from $p$ through the $q_i$ that $p$ sees. Each use of exact distance two has a witnessed two-edge walk and a nonedge by layer membership or the specified neighborhood restrictions.

The direct spanning-path argument in `path/path.md` handles the adjacent one-miss case at $w=5,r=6$. Each of the five listed eight-vertex paths uses every core vertex exactly once and starts at the requested private vertex. The endpoint for the other private vertex follows by exchanging the anchors and their private vertices. In the six-vertex argument the four degree-at-least-four vertices induce a complete graph with a matching removed. If the two other vertices are nonadjacent, the proof partitions the four high-degree vertices into two pairs in their respective neighborhoods, and a cross perfect matching supplies the needed cycle edges. If the two other vertices are adjacent, each of the three listed induced graphs on the four high-degree vertices supplies a spanning path between suitable neighbors of the two others. Deleting a cycle edge at a designated vertex then provides the required endpoint.

The application gives the required two middle neighbors per common vertex. If a common vertex had at most one middle neighbor, degree forces it adjacent to both nonpure remotes. Each pure remote then lies at distance two from it, as does $z$ and at least one missed middle vertex. The private endpoint condition follows from the distinct witnesses supplied by both opposite pure remotes, the three common vertices, and $z$ when a private vertex has no middle neighbor. For the six-vertex graph, isolation of a nonpure remote would force all five middle neighbors. If a nonpure remote $s$ has exactly one remote neighbor $t$, the distance-two witnesses at $s$ exhaust its cap unless there are exactly four pure remotes and $t$ is one of them. The other nonpure remote then cannot see $t$ or share a middle neighbor with $s$. Since $s$ sees at least four middle vertices, that other remote has at most one middle neighbor and three remote neighbors, violating its degree lower bound. The gluing edge joins the designated private vertex to a pure remote with the corresponding middle support. The two paths have disjoint vertex sets and together cover all fourteen vertices.

Consequently the four handwritten exclusions and the direct path construction, applied to the verified layout split, establish traceability throughout the degree-two order-fourteen case at second-smallest degree five and diameter at most three. These final arguments are handwritten. They use neither a Hall hypothesis nor a graph closure theorem.

## Sharp lower threshold

The strengthened bound fails for $s=3$ even with diameter three, adjacent anchors, and one miss each. On vertices $0,\ldots,8$, take the undirected edges
$$
01,02,12,13,15,24,25,34,35,36,38,45,46,47,56,67,68,78.
$$
For $z=0$, the two anchors are $1,2$, $W=\{3,4,5\}$, and $R=\{6,7,8\}$. The degrees are $(2,4,4,5,5,5,5,3,3)$, and the distance-two counts are $(3,3,3,3,3,3,2,3,3)$. The diameter is three and $|R|=3>2s-4$.
