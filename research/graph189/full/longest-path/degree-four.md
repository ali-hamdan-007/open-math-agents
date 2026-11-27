# Further restrictions when the minimum degree is four

Use the near-spanning, rooted component, and attachment results in [the attachment argument](attachments.md) and `gap-packing.md`. Suppose \(G\) is 2-connected, satisfies the distance-two cap, has \(\delta=4\) and order \(n\leq3k+2\), and is not traceable. Then \(k\geq8\), a longest path \(P\) omits only the low vertex \(z\), and a longest path \(Q\) through \(z\) omits a single Hamilton-connected component \(C\) of order \(m\) satisfying
\[
  \lfloor k/2\rfloor+1\leq m\leq k-2,\qquad m(k-m)\leq3k-2.
\]

## Eliminating \(m=k-2\)

The smallest of the three gaps between the four attachment indices of \(z\) on \(P\) has width at most \(k-1\), since the indices span at most \(n-4\leq3k-2\). If \(m=k-2\), the splice through \(z\) over a shortest gap is already maximal through \(z\). Use this splice as \(Q\); its omitted component \(C\) is the deleted block and \(z\) has no neighbor in \(C\), since the gap was between consecutive attachment indices. Both path positions immediately adjacent to \(z\) in \(Q\) have a neighbor in \(C\). The union \(U\) of their sets of neighbors in \(C\) lies at distance two from \(z\). The eight shifted distance-two witnesses from the original \(P\) meet \(C\) in just its first and last vertices. Thus \(|U|+6\leq k\), or \(|U|\leq m-4\).

There are \(L=n-m-3\leq2k+1\) internal positions of \(Q\) excluding \(z\), partitioned into its two sides. Each side has an attachment at its root-adjacent position. Every vertex of \(C\) needs at least \(k-m+1=3\) attachments, making at least \(3m\) incidences.

- If each side contains a position with precisely one neighbor in \(C\), the sum of the side bounds is at most \(L\leq2k+1<3m\).
- If neither side contains such a position, there are at most \(2+\lfloor(L-2)/(m+1)\rfloor\leq4\) attachment positions altogether, by the separation of positions with more than one neighbor in \(C\). Some vertex of \(C\) misses both root-adjacent positions, because \(|U|\leq m-4\). This vertex has at most two attachments, a contradiction.
- If just one side contains such a position, the other side's root-adjacent position has at least two neighbors in \(C\) and contributes at most \(m-4\) incidences. Let \(M\) denote the total number of positions with at least two neighbors in \(C\). The two side bounds, keeping their \(-M\) terms and subtracting the missing four incidences at the root-adjacent position, give a total of at most \(L+m-M-4\leq3k-5-M\). Thus \(3m\) incidences require \(M=1\). This sole position provides at most \(m-4\) incidences. All other attachments have exactly one neighbor in \(C\), occur on one side, and are nonconsecutive: two consecutive positions would either insert their common neighbor or, if their neighbors differ, splice a spanning path of \(C\). They therefore give at most \((L+1)/2\) additional incidences. The total is at most \(m-4+(L+1)/2\leq2k-5<3m\).

Hence \(m\ne k-2\).

## Endpoint rotations and the finite certificate

Write \(P=(v_1,\dots,v_{n-1})\) and let \(i_1<\cdots<i_4\) be the indices of the four neighbors of \(z\). For any longest unrooted path the gaps are at least \(m+1\), since a shorter one would allow a splice through \(z\) that improves on the rooted optimum. The two tails \(l=i_1-1\) and \(r=n-1-i_4\) are positive. We may reverse \(P\) to put the shorter tail on the left.

If \(v_1\) is adjacent to \(v_t\), then \((v_{t-1},v_{t-2},\dots,v_1,v_t,v_{t+1},\dots,v_{n-1})\) is another longest path. If \(i_{j-1}<t\leq i_j\) for \(j\in\{2,3,4\}\), the rotated indices of \(v_{i_1}\) and \(v_{i_j}\) are \(t-i_1\) and \(i_j\), consecutively among the four neighbor indices. Their difference must be at least \(m+1\). Thus the last \(\max(0,m-l)\) pivot positions in each such interval are forbidden as neighbors of \(v_1\). The four positions \(t=i_j+1\) are also forbidden, because the resulting rotated path would start at a neighbor of \(z\) and could then be extended. These four positions are disjoint from the three forbidden interval ends: the first position following any attachment index is outside the last \(\max(0,m-l)\) positions in its interval, by the gap lower bound and \(l\geq1\). As the endpoint has degree at least \(k\), all of its neighbors lie on \(P\), and hence
\[
 k+3\max(0,m-l)+4\leq n-2.
\]
For \(k\geq15\), the packing bound and the exclusion \(m\neq k-2\) imply \(m=k-3\), because \(4(k-4)>3k-2\) and the product \(m(k-m)\) decreases for \(m>k/2\). The three gaps are then at least \(k-2\), so the combined tails are at most six and \(l\leq3\). The endpoint inequality gives \(k+3(k-6)+4\leq3k\), or \(k\leq14\), a contradiction.

For \(8\leq k\leq14\), the finite certificate uses only the positions of the four neighbors of \(z\) along a longest path. A state is a tuple of four internal indices whose consecutive gaps are at least \(m+1\), identified with its reversal. A pivot \(t\) of the first endpoint transforms each original index \(i<t\) to \(t-i\) and leaves every \(i\geq t\) fixed. Discard pivots leading out of the current state set; the opposite endpoint cannot be a pivot, since adjacent endpoints could close a cycle on \(G-z\), which can be opened at a neighbor of \(z\) and preceded by \(z\). The same test is applied from the other endpoint. Any state realized by a longest path has at least \(k\) pivots from each end that lead to other realized states, counting pivot positions individually even when two lead to the same state. Thus iteratively removing states with fewer than \(k\) pivots on either side never removes a realized state.

The calculation in `pivot/rotation_core.py` scans all orders at most the stated bound at each \(k\), using the packing inequalities as its parameter bounds. It leaves exactly the five order triples listed below. The independent implementation in `tight/audit-rotation.py` enumerates binary position words and computes the same fixed point. Its certificate audit is in `tight/pivot-audit.md`.

## Resolving the five endpoint-profile residuals

The separate endpoint-rotation certificate leaves the triples
\[
(k,n,m)=(9,28,5),\ (9,29,5),\ (10,32,6),\ (11,34,6),\ (11,35,6).
\]
We give a direct contradiction for these five triples. The internal degree bound from `gap-packing.md` forces \(C\) to be a clique in every case, because \(m-1=\lfloor k/2\rfloor\).

Here a position of \(Q\) with exactly one neighbor in \(C\) yields a stronger incidence bound. On the same side of \(z\), no two consecutive path vertices can both be attachment positions. If they have the same sole neighbor, that neighbor can be inserted. Otherwise a spanning path of \(C\) between two distinct contacts can be inserted. Thus, for a side with \(S>0\) single-contact positions and \(M\) positions having at least two contacts, all \(S+M-1\) gaps between successive attachment positions contain at least one empty position, and at least \(M\) of them contain at least \(m\). If the number of internal positions on the side is \(L\), we have \(L\geq2S+(m+1)M-1\), so its incidence count is at most \(L-S-M+1\). On the other side, with \(L'\) internal positions and \(M'\) positions having at least two contacts, the earlier bound gives at most \(L'+m-M'\) incidences. Therefore if at least one single-contact position exists anywhere, the total count is at most \(n-1-b\), where \(b\) is the total number of attachment positions. This follows from \(L+L'=n-m-2\), and is an upper bound even if the other side has single-contact positions as well if we keep that side's \(-S'\) term using \(m\geq1\). Each vertex of \(C\) has at least \(k-m+1\) attachments, so \(b\geq k-m+1\). On our five triples the upper bound \(n-1-b\) is less than the required \(m(k-m+1)\). Thus every attachment position has at least two contacts.

Equation (5) of `gap-packing.md` now gives at most five attachment positions in each triple. The two cases \(k=11\) are impossible because each vertex of \(C\) needs six attachments. For \(k=9,10\), every vertex of \(C\) needs five attachments and therefore sees precisely the same five positions. Let \(A\) be this common five-vertex neighborhood outside \(C\). Then \(z\notin A\) since its degree four is less than \(m\).

The five positions of \(A\) cannot all occur on one side of \(z\) on \(Q\), since the required \(4(m+1)+1\) internal positions there would exceed the available \(n-m-2\). With both sides nonempty, \(z\) is internal and there are \(n-m-3\) usable internal positions after excluding it. On the two nonempty sides their minimum joint span is \(3(m+1)+2\), leaving at most one additional internal position when \(k=9\), and none when \(k=10\). If neither position immediately adjacent to \(z\) on \(Q\) were in \(A\), two additional internal positions would be necessary. Thus \(z\) has a neighbor in \(A\), placing every vertex of \(C\) at distance two. Since \(m=k-4\), at most four distance-two vertices from \(z\) lie outside \(C\).

Write \(U=N(z)\). In fact \(U\subseteq A\): any \(u\in U\setminus A\) has no neighbors in \(C\), so every neighbor of \(u\) lies in \(\{z\}\cup(U\setminus\{u\})\cup(D_2(z)\setminus C)\). That set has size at most \(1+3+4=8<k\), contradicting high degree. Thus \(A\setminus U\) consists of one vertex \(a\).

Now return to any longest unrooted path \(P\), which omits just \(z\). At least four of its eight shifted distance-two witnesses from \(z\) lie in \(C\). Consider the runs of consecutive vertices of \(C\) on \(P\). A run cannot have a member of \(U\) on each side. Those two members would be consecutive attachments of \(z\), with at least \(m\) vertices between them by maximality of \(Q\). The single run would then exhaust \(C\), making only its first and last vertices shifted witnesses, contrary to four. Hence every run contributes at most one shifted witness, so there are at least four runs.

Every internal run has two neighbors along \(P\) outside \(C\), both in \(A\), and neither can have both neighbors in \(U\). Therefore every internal run has \(a\) on at least one side. There are at most two internal runs, because \(a\) has only two path neighbors. At least four runs occur in total, so both endpoints of \(P\) lie in \(C\). Their edge in the clique closes a cycle covering \(G-z\). Opening the cycle at any neighbor of \(z\) and prepending \(z\) gives a spanning path, the final contradiction.

Thus every 2-connected graph satisfying the distance-two hypothesis with minimum degree at least four and order \(n\leq3k+2\) is traceable, using `gap-packing.md` when the minimum degree is at least five. For the full even-distance hypothesis, Easwar–Johari's Theorem B covers graphs outside the 2-connected case.
