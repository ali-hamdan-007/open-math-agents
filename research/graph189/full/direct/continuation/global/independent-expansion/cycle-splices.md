# Splicing a cone factor with two cycles

The cone on a qualifying graph \(G\) has an added universal vertex. A 2-factor of the cone with two cycles gives a path \(P\) and a cycle \(C\) partitioning \(V(G)\), by opening the cycle through the new vertex. Write \(p=|P|\), \(m=|C|\), \(n=p+m\), \(k\) for the second-smallest degree, and \(\kappa\) for vertex connectivity. Under the Graph 189 hypotheses at \(k\ge11\) and \(\kappa\ge2\), the existing [longest-path gap](../../../lowblock/all-near-spanning.md) says that every path of a counterexample omits at least \(\ell=\lceil k/2\rceil+2\) vertices.

If \(k\ge11\), \(\kappa\ge3\) and \(n\le3k+2\), the existence of a two-cycle cone factor forces \(G\) to be traceable. More generally, for \(k\ge13\) and \(n\le5k\), a counterexample with a two-cycle cone factor must have \(m\ge k-8\). When \(C\) is Hamilton-connected, the bound strengthens to

\[
m\ge k+2-\left\lfloor\frac{4k-1}{\ell}\right\rfloor .
\]

The exact finite inequalities below can give sharper bounds, and apply starting at \(k=11\).

## Path contacts and their spacings

First \(m\ge\ell\), since \(P\) itself omits exactly \(C\). Neither endpoint of \(P\) can meet \(C\), because an edge from the endpoint to \(C\) would let us open and append the entire cycle. Nor does the subgraph on \(P\) have a spanning cycle. Such a cycle could be opened and joined to \(C\) across any crossing edge, which exists by connectivity. If a path endpoint is low, it has a neighbor on \(P\) besides its immediate neighbor because \(\kappa\ge2\). An edge to the opposite endpoint would be a spanning cycle on \(P\), and any other such edge rotates the path to have two high endpoints. For that rotated path the two endpoint degree counts sum to at least \(2k\), all inside \(P\). If the sum were at least \(p\), a neighbor position of one endpoint and a complementary predecessor position of the other would produce a spanning cycle on \(P\). Hence \(p\ge2k+1\). We can use the rotated path in the sequel.

Mark the vertices of \(P\) that meet \(C\), and let \(q\) count the marks. In the ordered list of marks combine successive positions having the same singleton \(C\)-neighbor into one group. A position with at least two neighbors in \(C\) is a group by itself. Denote the number of groups by \(g\). Let \(a=\max(0,k-m+1)\). Every high vertex of \(C\) has at least \(a\) contacts in \(P\), so \(q\ge\max(g,a)\). Also \(g\ge\min(\kappa,m)\). If \(g<m\), remove one vertex per group, namely its owner for a singleton group or its mark for a multiple group. This disconnects \(C\) from \(P\), and both sides survive because the two extreme vertices of \(P\) are unmarked.

At each tail of \(P\) there are at least \(\ell\) unmarked vertices before the first mark from its end. Otherwise one opens \(C\) at a neighbor of the mark and traverses \(C\) and the rest of \(P\), omitting only the shorter tail. For consecutive groups their two boundary marks have distinct available neighbors in \(C\). A path on \(C\) between those neighbors can use the longer of the two cycle arcs, which misses at most \(\lfloor m/2\rfloor-1\) vertices of \(C\). Splicing this arc into \(P\) in place of the intervening gap makes that gap cost at least \(L=\max(0,\ell+1-\lfloor m/2\rfloor)\) vertices. Consequently

\[
p\ge 2\ell+q+(g-1)L .
\]

In the Hamilton-connected case one can use all of \(C\) between any two distinct contacts, so the same bound holds with \(L=\ell\).

## A dense core in the exterior cycle

If every high vertex of \(C\) owns a singleton group then \(g\ge m-1\). Otherwise a high vertex without such a group has at least \(a\) contacts, all among the multiple groups. Thus there are at least \(a\) multiple groups and \(g\ge a\). Remove the owners of all singleton groups and the possible low vertex of \(C\), obtaining a subgraph \(H\). The number of removed vertices is at most \(r=g-a+1\). Every member of \(H\) is high and has at most \(g\) neighbors in \(P\), all at multiple marks. Therefore

\[
|H|\ge m-r,\qquad \delta(H)\ge k-g-r_\mathrm{actual},
\]

where \(r_\mathrm{actual}=m-|H|\le r\). If \(m-r\ge2\) and \(2k-2g-r\ge m+1\), it follows that \(2\delta(H)\ge|H|+1\), making \(H\) Hamilton-connected by the Hamilton-connected form of Ore's theorem. Any two distinct vertices of \(C\) can be joined by a path covering \(H\). For this, take disjoint portions of the original cycle from the two specified vertices to distinct first landings in \(H\), with no internal vertex in \(H\). If an endpoint already belongs to \(H\), use a zero-length portion there. If neither belongs to \(H\), the two arcs between the endpoints either each meet \(H\), or one arc contains all of \(H\) and can be entered from both ends. In either case the landings can be taken distinct. A Hamiltonian path in \(H\) joins the two portions. Consequently the gap bound improves to

\[
p\ge2\ell+q+(g-1)\max(L,\ell-r).
\]

This gives a test on each possible \(g\). The script [two-cycle-bounds.py](two-cycle-bounds.py) replays the integer implications. For example at \(k=26\) it excludes \(m\le20\) through order \(130\) and \(m\le21\) through order \(126\). It tests necessary conditions, so a surviving pair of orders does not assert that a graph realizes it.

## Uniform bounds for \(n\le5k\)

Assume \(k\ge13\) and \(\ell\le m\le k-1\). Put \(d=k-m\), so \(a=d+1\). Then \(L=\ell+1-\lfloor m/2\rfloor>0\). If every high vertex owned a singleton group, \(g\ge m-1\) would give

\[
n\ge k+1+2\ell+(m-2)(\ell+1-m/2)>5k.
\]

The strict bound follows by concavity in \(m\). At \(m=\ell\) the right side is at least \(3k+5+k^2/8\), and at \(m=k-1\) it is at least \((11k-11)/2\). Both exceed \(5k\) for \(k\ge13\). Thus \(g\ge a\) and \(r=g-d\) is a valid bound on the excluded core vertices.

Suppose \(d\ge9\), put \(t=g-1\), and set \(M=p-2\ell-1\). Using \(q\ge g\) gives \(d\le t\le M/(L+1)\) and \(M\le3k+d-5\). Here \(L+1\ge9\), so \(3g\le k+d/3+4/3\le k+2d-1\). This is the dense-core condition. The core has at least \(k-g\ge2\) vertices since \(m\ge\ell\) and \(3g\le k+2d-1\). Its improved gap bound, again using \(q\ge g\), gives \(t(\ell+d-t)\le M\).

The last inequality fails at both ends of the interval for \(t\). At \(t=d\) the value \(d\ell\) already exceeds \(3k+d-5\). At \(t=B=M/(L+1)\), the factor \(\ell+d-B\) exceeds \(L+1\), because

\[
\ell+d-B\ge k/6+8d/9+23/9>d/2+5\ge L+1.
\]

Concavity then rules out the entire interval. Thus \(m\ge k-8\). When \(C\) is Hamilton-connected, the initial \(L=\ell\) bound rules out the all-owners alternative already for every \(k\ge11\), since \(n\ge m+(m-1)+m\ell>5k\). A high nonowner gives \(g,q\ge k-m+1\) when \(m\le k\), so \(n\ge k+1+(k-m+2)\ell\). Rearranging gives the stated stronger bound.

## Two-cycle factors through order \(3k+2\)

Suppose \(k\ge11\), \(\kappa\ge3\), and \(n\le3k+2\). The path bound \(p\ge2k+1\) gives \(m\le k+1\), so \(d=k-m\ge-1\) and \(L\ge3\). We have \(g\ge3\) by the cut bound. If all high vertices owned singleton groups, then \(n\ge5m+2\ell-7\ge7\ell-7>3k+2\). Therefore the core construction applies with \(a=d+1\) and \(r=g-d\).

The initial spacing and mark counts give \(p\ge2\ell+4g-3\). Thus \(4g\le k+d+1\) for \(k\ge12\), yielding \(3g\le k+2d-1\) since \(k+5d\ge7\). At \(k=11\) the same spacing gives \(4g\le k+d\) because \(2\ell=k+5\), and \(k+5d\ge4\) again yields the core condition. The core has at least \(k-g\ge2\) vertices. The improved spacing now gives

\[
t(\ell+d-t)\le p-2\ell-1\le k+d-3,\qquad t=g-1 .
\]

But \(2\le t\le B=(k+d-3)/4\). At \(t=2\) the left side is at least \(k+2d>k+d-3\). At \(t=B\) we have \(\ell+d-B\ge(k+3d+11)/4>4\), again giving a value above \(k+d-3\). By concavity there is no such factor in a counterexample. This does not require \(C\) to be Hamilton-connected.

## A factor that needs more than one two-edge switch

The [independent-expansion equality graph](independent-expansion.md) provides an explicit example at every \(k\ge11\) and \(\kappa\in\{2,3,4\}\). The graph consists of the \(k\)-clique \(S\) joined to an independent set \(J\) of size \(k-\kappa+1\), together with a clique \(R\) of size \(k+\kappa\). The only crossing edges between \(S\cup J\) and \(R\) are all the edges between \(S\) and a \(\kappa\)-set \(Q\subset R\).

In the cone, form a cycle through the apex and a spanning path of \(S\cup J\) with both ends in \(J\). To make such a path, place at least one \(S\) vertex between each pair of successive \(J\) vertices, putting the remaining \(S\) vertices in one gap. Form the other factor cycle in \(R\) by alternating \(Q\) with distinct vertices of \(R\setminus Q\), and appending the residual vertices of \(R\setminus Q\). No consecutive cycle vertices both belong to \(Q\).

A switch deleting one edge from each cycle and reconnecting them would need both vertices of the \(R\)-edge to belong to \(Q\), except that it can use one apex cross edge if the first cut edge meets the apex. In that exception the other endpoint of the first cut edge lies in \(J\) and has no \(R\)-neighbor. Hence neither type of direct switch exists. One can first switch two edges within the clique \(R\) to make two members of \(Q\) consecutive. The first cycle has an \(S\)-\(S\) edge in its long gap, which then switches with the new \(Q\)-\(Q\) edge to merge the cycles. The [switch replay](cone-switch-replay.py) checks the absence of all direct switches and the two explicit moves at nine representative orders.

These deductions concern two-cycle factors and local splicing. The results leave the general case of a cone factor with several exterior cycles open.
