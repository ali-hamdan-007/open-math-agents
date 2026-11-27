# Diameter three and degree two, with one missed middle vertex at each anchor

Let \(G\) be a finite simple graph of diameter at most three. Let \(z\) have degree two, with neighbors \(a,b\), and let \(W,R\) be the distance-two and distance-three layers from \(z\). Write \(\sigma\ge4\) for the second-smallest degree. Assume that each vertex has at most \(\sigma\) vertices at distance two and that \(n\ge 2\sigma+4\). Hence every vertex other than \(z\) has degree at least \(\sigma\), and \(|W|\le\sigma\).

Assume that \(a\) misses exactly one vertex \(p\) of \(W\), and that \(b\) misses exactly one vertex \(q\) of \(W\). These vertices are distinct, because each \(W\) vertex sees at least one anchor. Put \(C=W\setminus\{p,q\}\). Let \(P\) and \(Q\) be the remotes with \(W\)-neighborhoods \(\{p\}\) and \(\{q\}\), respectively. Let \(E=P\cup Q\) and \(S=R\setminus E\). Write \(r=|R|\), \(e=|E|\), and \(m=|S|\).

## Bounds and the exclusive-remote cycle

Since \(a\) has one missed middle vertex, \(d(a)\ge\sigma\) gives \(|W|\ge\sigma-1\) if the anchors are adjacent, and \(|W|=\sigma\) if they are nonadjacent. In particular \(r\ge\sigma+1\).

Each anchor counts at least one vertex at distance two outside \(R\): its missed middle vertex if the anchors are adjacent, or the other anchor if they are nonadjacent. Since all of \(Q\cup S\) is at distance two from \(a\), and all of \(P\cup S\) is at distance two from \(b\), we obtain
\[
 |P|+m\le\sigma-1,\qquad |Q|+m\le\sigma-1,\qquad
 |P|,|Q|\ge r-\sigma+1\ge2.
\]
Every vertex of \(E\) has at least \(\sigma-1\) neighbors in \(R\), having only one neighbor outside \(R\). Since \(|P|+m,|Q|+m\le\sigma-1\), every element of \(P\) has a neighbor in \(Q\) and conversely. Thus \(Q\) is at distance two from \(p\), and \(P\) from \(q\).

The graph induced by \(E\) is Hamiltonian. In fact \(r+m\le2\sigma-2\) by adding the anchor budgets, so
\[
 \delta(G[E])\ge\sigma-1-m\ge(r-m)/2=e/2.
\]
Dirac's theorem applies as \(e\ge4\). Deleting a cycle edge gives a spanning path with any prescribed endpoint in \(E\).

Both \(p\) and \(q\) have a neighbor in \(C\). If \(p\) misses all \(C\), then \(z,C,Q\) are all at distance two from \(p\), using \(b\) for \(z\) and \(C\). If the anchors are nonadjacent this gives at least \(1+(\sigma-2)+2=\sigma+1\). If they are adjacent, \(a\) is also at distance two from \(p\) through \(b\), giving at least \(2+(\sigma-3)+2=\sigma+1\). Interchange the labels for \(q\). Consequently, whether the anchors are adjacent or not, each private vertex counts the opposite anchor at distance two.

**Exclusive and outer-layer bounds.** In the one-miss layout,
\[
e\le\sigma-1,\qquad
|R|\le\left\lfloor(3\sigma-3)/2\right\rfloor,\qquad
|V(G)|\le\left\lfloor(5\sigma+3)/2\right\rfloor,\qquad
m\ge r-\sigma+1.
\]
To see the first inequality, suppose \(e\ge\sigma\). No common middle vertex can see both \(p,q\), since then it would count \(E\cup\{z\}\) at distance two. Sum the distance-two counts at \(p\) and \(q\): every vertex of \(E\) counts once through an opposite exclusive neighbor in \(R\), every vertex of \(C\) counts at least once through an anchor, \(z\) counts twice, and the opposite anchors count twice. The total is at least \(e+|C|+4\ge2\sigma+1\), because \(|C|\ge\sigma-3\). This contradicts the two caps. Combining \(e\le\sigma-1\) with \(e\ge2(r-\sigma+1)\) proves the remaining inequalities.

## An infinite traceable subcase

**Theorem.** Under the hypotheses above, if \(\sigma\ge8\) and \(m=2\), then \(G\) is traceable. Both placements of the anchors are allowed.

Indeed \(r=e+2\le\sigma+1\), so \(r=\sigma+1\), \(e=\sigma-1\), and \(|W|=\sigma\). Each vertex of \(E\) has degree at least \(r-2\) inside \(R\).

The induced graph \(G[R]\) has minimum degree at least two. If an \(s\in S\) were isolated inside \(R\), its total degree would force it to see all of \(W\). Then it would count both anchors and every other remote at distance two, a contradiction. If \(s\) has just one neighbor \(t\) in \(R\), each vertex of \(E\setminus\{t\}\) is adjacent to \(t\): it already misses \(s\), and its degree inside \(R\) is at least \(r-2\). Such an \(s\) thus counts both anchors and all of \(E\setminus\{t\}\) at distance two. The cap forces \(t\in E\), where these vertices already exhaust the count \(\sigma\). Let \(s'\) denote the other vertex of \(S\). It cannot see \(t\) or share a \(W\)-neighbor with \(s\), since otherwise it would add a vertex at distance two from \(s\). As \(s\) sees at least \(\sigma-1\) vertices of \(W\), \(s'\) has at most one neighbor there. It has at most \(r-3=\sigma-2\) neighbors in \(R\), missing both \(s,t\), so its total degree is at most \(\sigma-1\). This is again a contradiction.

A graph on \(r\ge6\) vertices with minimum degree at least two and at most two vertices below degree \(r-2\) has a Hamiltonian cycle. This follows directly from Bondy–Chvátal cycle closure: each missing edge incident to a vertex of degree at least \(r-2\) has degree sum at least \(r\). After adding all such edges, each of the remaining two vertices has degree at least \(r-2\), so their edge also enters the closure. In particular \(G[R]\) has a spanning path starting at any prescribed \(r_0\in P\).

For a common \(c\in C\), if \(c\) sees both vertices of \(S\), every element of \(E\) is at distance two from \(c\) because each misses at most one other vertex of \(R\). This consumes the distance-two cap together with \(z\). Every other vertex of \(W\) shares an anchor with \(c\), so \(c\) must see all of \(W\setminus\{c\}\). If \(c\) sees at most one vertex of \(S\), its total degree bound gives \(d_W(c)\ge\sigma-3\) since it sees two anchors. Thus \(\delta(G[C])\ge\sigma-5\ge|C|/2\), and \(G[C]\) is Hamiltonian. Choose a spanning path in \(C\) starting at a neighbor of \(p\). The sequence
\[
p,\ \text{the spanning path through }C,\ b,z,a,q
\]
is a path through the anchor block \(W\cup\{z,a,b\}\). Reverse this path and append the \(R\)-spanning path across the edge \(pr_0\). The two supports are disjoint and cover \(V(G)\), giving the claimed Hamiltonian path.

## An explicit family outside the earlier regimes

Use the order-fourteen easily verified witness from `parallel/fresh-wow/search_189_order14.txt`. In its labeling, \(z=0,a=1,b=2,p=3,q=4\), \(W=\{3,4,5,6,7\}\), and \(R=\{8,9,10,11,12,13\}\). The exclusive remotes are \(8,9,10,11\), and \(12,13\) are the mixed remotes. The two chosen vertices \(6,8\) are nonadjacent. Vertex \(6\) sees both anchors, every other middle vertex, and the two mixed remotes. Vertex \(8\) sees the other three exclusive remotes, including vertex \(9\), whose degree is five.

Replace each of \(6,8\) by a clique of \(t+1\) true twins, preserving every adjacency between that clique and the other original vertices. Each nonzero original vertex is either in a clique or adjacent to at least one of the two cliques. Therefore every nonzero vertex gains at least \(t\) in degree, and vertex \(9\) gains exactly \(t\). Thus the second-smallest degree is \(\sigma=5+t\), and the order is \(14+2t=2\sigma+4\).

Distances between original roles stay unchanged, since paths lift by choosing representatives and paths project to walks after deleting consecutive repetitions. Distinct vertices of the same clique are adjacent. No original role is at distance two from both \(6\) and \(8\): the pair covers all nonzero vertices by equality or adjacency, and \(z\) is at distances two and three from the pair. Hence blowing up the two roles increases each distance-two count by at most \(t\); the cap holds at \(\sigma=5+t\), and the diameter stays three. The two mixed vertices remain mixed, since the added remotes copy the exclusive \(W\)-neighborhood of \(8\), and each new middle vertex copies a common vertex. The two-connectivity of the witness persists under true-twin addition: deleting a new twin leaves the old graph, while deleting an old vertex leaves the old graph minus that vertex and each remaining twin attached to it. If the replaced role itself was deleted, the other twins still have its surviving neighbors.

Easwar and Johari [arXiv:2609.11719](https://arxiv.org/abs/2609.11719) cover diameter at most two, order at most \(2\sigma+3\), and graphs that are not two-connected. These blow-ups have diameter three, order \(2\sigma+4\), and are two-connected. The prior degree-two checks give the order bound \(3\sigma-1\) for \(\sigma\ge4\), with the earlier handwritten analysis additionally bounding \(|R|\) by \(2\sigma-4\). Our one-miss bound \(\lfloor(3\sigma-3)/2\rfloor\) is strictly lower than \(2\sigma-4\) for \(\sigma\ge6\). The traceability theorem covers the full two-mixed one-miss subcase for all \(\sigma\ge8\), including this infinite family. It leaves other one-miss layouts, unequal or two-miss layouts, and the other minimum-degree branches open.

## Every full-middle adjacent one-miss graph at order \(2\sigma+4\)

**Theorem.** Independently of the number of mixed remotes, an adjacent one-miss layout with \(|W|=\sigma\) and \(n=2\sigma+4\) is traceable.

By Easwar and Johari's theorem, assume \(G\) is two-connected. Each anchor has initial degree \(\sigma+1\). Pick distinct \(p_1,p_2\in P\) and distinct \(q_1,q_2\in Q\). Use their Lemma 3.3 to add the four edges in this order:
\[
ap_1,\quad bq_1,\quad ap_2,\quad bq_2.
\]
For the first two edges, the endpoints have disjoint neighborhoods and degree sum at least \(2\sigma+1=n-3\). The opposite anchor has been linked only into its own exclusive class, so it cannot create a common neighbor. For the third and fourth edges, the corresponding anchor has gained degree one, giving degree sum at least \(2\sigma+2=n-2\). Its only possible common neighbor with the target vertex is the preceding same-class remote. Lemma 3.3(1) or (2), respectively, makes each addition preserve traceability.

Both anchors now have degree at least \(\sigma+3\), so ordinary traceability closure at degree sum \(n-1\) makes each anchor adjacent to every other vertex. Every vertex of \(R\) has thereby gained two neighbors and now has degree at least \(\sigma+2\). Ordinary closure completes \(G[R]\). Since \(r=\sigma+1\) and every \(r\in R\) already had a neighbor in \(W\), every remote now has degree at least \(\sigma+3\). Ordinary closure completes the \(R\)–\(W\) adjacencies, then the remaining \(W\) edges. The resulting graph contains a complete graph on all vertices other than \(z\), so it has a spanning path beginning at \(z\).

The use of Easwar and Johari's local closure lemma here starts at order \(2\sigma+4\), one beyond their order theorem. In comparison, the direct two-block theorem also covers the nonadjacent one-miss layout when there are exactly two mixed remotes and \(\sigma\ge8\).
