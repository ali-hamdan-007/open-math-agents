# Three-cycle cone factors in the moderate order range

Let \(G\) satisfy Graph 189 with second-smallest degree \(k\), vertex connectivity \(\kappa\), and order \(n\le3k+2\). Suppose a minimum-cycle 2-factor of its cone consists of three cycles. Opening the apex cycle gives a path \(P\) and two exterior cycles \(A,B\) that partition \(V(G)\).

* If \(k\ge11\), \(\kappa\ge2\), and an edge joins the exterior cycles, then \(G\) has a Hamiltonian path. Neither exterior cycle needs to induce a Hamilton-connected graph.
* If \(k\ge26\), \(\kappa\ge3\), and the larger exterior cycle induces a Hamilton-connected graph, then \(G\) has a Hamiltonian path, irrespective of the edges between the two cycles.

The deductions use the [longest-path gap](../../../lowblock/all-near-spanning.md). Write \(h=\lceil k/2\rceil\) and \(\ell=h+2\). In a counterexample any actual path omits at least \(\ell\) vertices. A high vertex has degree at least \(k\), with at most one exception in all of \(G\).

## The apex path

Let \(p=|P|\), \(m=|A|\), and \(s=|B|\). The endpoints of \(P\) have no neighbors in either exterior cycle. Such an edge would append that entire cycle to \(P\) and reduce the number of cone factor cycles. The subgraph on \(P\) cannot contain a spanning cycle either. Connectivity gives an edge to some exterior cycle, and opening the two cycles at the ends of that crossing edge produces a longer apex path with one fewer exterior cycle.

If an endpoint of \(P\) is low, it has another neighbor on \(P\) besides its immediate neighbor because \(\kappa\ge2\). It cannot be adjacent to the other endpoint. Use its other neighbor to rotate the path to have two high endpoints. The cone factor still has minimum cycle count and none of its new endpoints meets an exterior cycle. The endpoint degree-sum argument now gives \(p\ge2k+1\), since a larger degree sum than \(p-1\) would close a spanning cycle on the path vertices. Thus \(m+s\le k+1\).

## Adjacent exterior cycles

Suppose there is a crossing edge. A switch exchanging two cycle edges for two crossing edges cannot merge \(A\) and \(B\) in the factor. Let \(d_B(x)\) count the \(B\)-neighbors of \(x\in A\). For two consecutive \(x,x'\) of \(A\), the successors on \(B\) of the neighbors of \(x\) must avoid the neighbors of \(x'\), since otherwise the cross edges and those two cycle edges give a switch. Hence \(d_B(x)+d_B(x')\le s\). Likewise consecutive vertices of \(B\) have cross degrees summing to at most \(m\).

We can choose a crossing edge \(xy\) with \(x\in A,y\in B\) and high cycle-neighbors \(a\) of \(x\), \(b\) of \(y\), such that

\[
d_B(a)\le s/2,\qquad d_A(b)\le m/2.
\]

To prove this, call a vertex heavy if its cross degree exceeds half the opposite cycle's order. A heavy vertex has only nonheavy cycle-neighbors by the degree-sum bounds. If neither side has heavy vertices or only one side does, choose any crossing edge or one incident with a heavy vertex on that side, respectively. At least one of the two cycle-neighbors of each endpoint is high. A crossing edge between heavy vertices works for the same reason. Otherwise choose any heavy \(x\in A\). More than half the vertices of \(B\) are its neighbors and all are nonheavy, so two of them are consecutive on the \(B\)-cycle. Take a high member of that pair as \(b\) and the other as \(y\). Take any high cycle-neighbor \(a\) of \(x\).

Opening \(A\) at \(ax\) and \(B\) at \(yb\) and joining through \(xy\) gives a path from \(a\) to \(b\) spanning both exterior cycles. Let \(X,Y\) be their respective sets of contacts in \(P\). Each is nonempty: for example \(d_B(a)\le s-d_B(x)\le s-1\), so

\[
|X|\ge k-(m-1)-(s-1)=k-m-s+2\ge1.
\]

Using the summed cross-degree bound gives \(|X|+|Y|\ge2k+2-3(m+s)/2\ge6\). All their marks have at least \(\ell\) vertices of \(P\) before and after them, since we may open our spanning exterior path at either end and append it to a path tail. Distinct marks from opposite sets have index difference at least \(\ell+1\). A smaller difference lets the exterior path replace their intervening gap and leaves fewer than \(\ell\) omissions.

The span of these two marked sets, counting both extremes, contains at least \(|X|+|Y|+\ell-1\) positions. Here is the intersection accounting. If their intersection has size \(r\) and there are pure marks of both types, the marked sequence has at least \(r+1\) consecutive pairs requiring index difference \(\ell+1\). Its span is at least \(|X|+|Y|-r+(r+1)\ell\). If there is just one pure type, then \(r\ge1\) and there are at least \(r\) such pairs. If all marks are common, then \(r\ge3\) and the span is at least \(r+(r-1)\ell\). Each lower bound implies the claim. One can count the required pairs by putting the pure runs of each type in groups and making each common mark its own group.

Including the two outer tails gives \(p\ge3\ell+|X|+|Y|-1\). Therefore

\[
n\ge 2k+1+3\ell-(m+s)/2
 \ge 2k+1+3(k/2+2)-(k+1)/2
 > 3k+2.
\]

This contradiction excludes all crossings between the exterior cycles in a minimum factor of a counterexample.

## Anticomplete exterior cycles

Suppose now that \(A,B\) are anticomplete, \(m\ge s\), and \(A\) is Hamilton-connected. Assume \(k\ge26\) and \(\kappa\ge3\). Then \(3\le s\le h\). Let \(L=\ell-s=h+2-s\). Group the \(A\)-marks on \(P\) as in [the two-cycle splice proof](cycle-splices.md), with one group for a run of a shared singleton \(A\)-neighbor and one for each mark with several neighbors. Let \(q,g\) count marks and groups. Each tail has at least \(L\) unmarked vertices, and the same holds between consecutive groups. Using a shorter tail or gap would let us splice all of \(A\), leave all \(s\) vertices of \(B\) unused, and miss fewer than \(\ell\) vertices overall. Thus \(p\ge(g+1)L+q\).

Every high \(A\)-vertex has at least \(a=k-m+1\ge s\) neighbors on \(P\), since there are no cross edges to \(B\). Hence \(q\ge a\). If a high vertex has no singleton group then it needs at least \(a\) multiple groups, while otherwise \(g\ge m-1\). Consequently \(g\ge s-1\). Also \(g\ge3\): if \(g<3\le m\), deleting one vertex per group separates the remaining \(A\) from \(P\cup B\), since \(A\) has no \(B\)-neighbor.

### Four through \(h-2\) vertices in the smaller cycle

If \(s=4\) and \(g\ge4\), the bound \(p\ge5(h-2)+a\) gives \(n\ge k+5h-5>3k+2\). With \(g=3\) a high vertex missing a singleton group is impossible because \(a\ge4\). If all high vertices own groups, \(m=4\) and there must be three high vertices owning the three singleton groups, with no multiple groups. Then \(q\ge3a\), giving \(n\ge3k+4h-9>3k+2\).

If \(5\le s\le h-2\), the bounds \(g\ge s-1\) and \(q\ge a\) give

\[
n\ge k+1+s(h+3-s).
\]

The concave product has value \(5h-10\) at both endpoints \(5,h-2\), and \(5h-10>2k+1\) when \(k\ge26\). This again exceeds the allowed order.

### A smaller cycle of order \(h-1\) or \(h\)

At least one outer tail or between-group gap has length exactly \(L\). If they were all longer, for \(s=h-1\) the inequality \(g\ge h-2\) would give \(p\ge4(g+1)+q\ge5h-6>4h+4\), above the order bound \(p\le3k+2-2s\). For \(s=h\), a high nonowner gives \(g\ge a\ge h\), so \(p\ge3(g+1)+q\ge4h+3>4h+2\). Otherwise every high vertex owns a group, and \(p\le4h+2\) forces \(g=h-1=m-1\), all groups singleton with distinct high owners. This forces \(q\ge h(h-1)>p\).

Splice all of \(A\) into \(P\) at a gap or tail of length \(L\), retaining the other original path vertices in at most two intervals. Their total order is at most \(4h+1\). Each high \(B\)-vertex has at least \(k-s+1-L=k-h-1\) contacts in these intervals. Put \(\Delta=\lceil s/2\rceil+1\). If two distinct high \(B\)-vertices have distinct contacts at index difference at most \(\Delta\) in one interval, the longer arc between those vertices on \(B\) can replace the intervening path segment. This second splice loses at most \(\lfloor s/2\rfloor-1\) vertices of \(B\), so the total omissions are at most \(L+(\Delta-1)+(\lfloor s/2\rfloor-1)=h+1\).

If no such pair exists, group the marks of high \(B\)-vertices in each retained interval. Gaps between distinct groups have index difference at least \(\Delta+1\). If there are \(j\in\{1,2\}\) nonempty intervals of marked vertices with total order at most \(4h+1\), their combined number of groups is at most \(j+(4h+1-j)/(\Delta+1)\le2+(4h-1)/(\Delta+1)<10\), using \(\Delta+1\ge(h+3)/2\). There are at least \(s-1\ge h-2\ge11\) high \(B\)-vertices. Some high vertex must lack a singleton group, so it has at most nine contacts across the retained intervals, contradicting \(k-h-1\ge11\).

### A triangle in the smaller cycle

Let \(s=3\). Then \(L=h-1\). If \(g\ge4\), the bound \(p\ge5(h-1)+a\) gives \(n\ge k+5h-1>3k+2\). Thus \(g=3\). If \(m\le4\), every high vertex must own a singleton group since \(a>3\); there are at least two high owners and at most one multiple group. Each of those two owners needs at least \(a-1\) private marks, and their combined demand and the multiple mark if present give \(q\ge2a-1\). It follows that \(n\ge2k-m+4h>3k+2\). Otherwise there are at least four high \(A\)-vertices, so a high nonowner requires \(a\le3\). With \(m+3\le k+1\), this forces \(m=k-2\), \(a=3\), and precisely three multiple marks, comprising a set \(S\) on \(P\). All high \(A\)-vertices meet all three. For each high \(A\)-vertex these are its only external neighbors, so it has all \(m-1\) internal neighbors. Thus \(A\) is a clique, including the possible low vertex.

Now \(p=2k+1\), \(n=3k+2\), and the four gaps and tails around \(S\) sum to \(2k-2\) vertices. Each has length at least \(h-1\). Consequently a gap has length exactly \(h-1\), and for odd \(k\) all four do, including the tails.

A high \(b\in B\) cannot meet \(S\). Choose another high vertex \(b'\) of the triangle. The successors of \(b\)'s contacts on \(P\) are disjoint from the contacts of \(b'\), because an overlap would give a switch joining the triangle to the apex cycle. Both sets are within distance two of \(b\), and their union leaves at least \(|N_P(b')|\ge k-2\) actual distance-two witnesses after removing \(b\)'s direct neighbors. If \(b\) met an \(S\)-mark it would also see at least \(m-1=k-3\) high members of \(A\) at distance two, exceeding \(k\).

Splice in the entire clique \(A\) over a gap of length \(h-1\), taking an outer tail for odd \(k\). The two high triangle vertices still have at least \(k-h-1\) contacts each in the retained \(P\)-intervals, whose total order is \(N=2k-h+2\). The ends of every interval are either original path endpoints or members of \(S\), and neither can be a high triangle contact. An adjacent pair of contacts for the same high \(b\) lets us insert \(b\), omitting only \(h-1+2=h+1\) vertices overall. A pair of contacts for distinct high triangle vertices at distance at most three on a retained interval lets us splice the full triangle, omitting at most \(h-1+2\) path vertices.

If neither splice is available, weight each occupied contact index by the number of these two high vertices it touches. A weight-two index is at distance at least four from any other occupied index, and any two consecutive occupied indices in marked order with weight one are at distance at least two. Thus the difference between consecutive occupied indices is at least the sum of their weights. In a retained interval of order \(N_i\), its unoccupied ends give span at most \(N_i-3\) between first and last occupied indices, so the total weight is at most \((N_i+1)/2\). Across at most two intervals this gives weight at most \((N+2)/2\), and at odd \(k\) at most \((N+1)/2\) by choosing the short tail. Both available bounds are less than \(2(k-h-1)\) in their respective parities for \(k\ge26\). This forces one of the two splices and finishes the triangle case.

The proofs leave anticomplete factors whose larger exterior cycle need not be Hamilton-connected, and factors with at least three exterior cycles, for further work.
