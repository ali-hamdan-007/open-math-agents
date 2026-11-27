# Three ports outside a pure component at a degree-four root

Let \(G\) be a finite 2-connected simple graph, let \(z\) have degree four, and let every other vertex have degree at least \(k\ge5\). Assume each vertex has at most \(k\) vertices at positive even distance and any two vertices other than \(z\) are at distance at most four. In the application to Conjecture 189, the last hypothesis follows from `five_endpoints` and `diameter_le_five` of the upstream reduction. Write \(A=N(z)\), \(T=N_2(z)\), and assume \(|V(G)|>3k+2\).

If the induced graph \(G-N[z]\) is disconnected, then exactly one component is contained in \(T\), and the other component has precisely two vertices in \(T\). In particular the three-port case cannot occur. Combined with the [two-port construction](degree-four-two-ports.md), the stated hypotheses imply that every nontraceable graph has connected \(G-N[z]\) in these orders.

## Forcing a component contained in the second layer

A port is a vertex of a component of \(G-N[z]\) with a neighbor in \(A\), equivalently a vertex of \(T\). Other vertices of the component are called remotes. Each component has at least \(k-3\) vertices since all its external neighbors lie in \(A\). It has at least two ports and at least two anchor neighbors by 2-connectivity. Deleting a unique port or unique anchor neighbor would separate the component from the rest of the graph. The component has another vertex after deleting a port because \(k-3\ge2\).

Suppose every component contains a remote. Take a remote \(x\) in one component. Each other component's remote is at distance exactly four from \(x\): every path between the components visits \(A\), each remote is at least two steps from \(A\), and the assumed upper bound on high-vertex distances is four. If there were \(k-1\) or more such opposite remotes, a shortest path to any of them would also supply an anchor at distance two from \(x\). The even budget would forbid any internal distance-two vertex. Along any shortest path inside the induced component to an internal nonneighbor, the second step would give just such a vertex, so \(x\) must be adjacent to all other vertices in its own component. It then sees both distinct anchor contacts of that component at distance two, which exceeds its even budget. Thus each component has at most \(k-2\) opposite remotes. Taking any two components and adding their two inequalities bounds the total number of remotes by \(2k-4\). Since \(|T|\le k\), this yields \(|V(G)|\le 5+k+(2k-4)=3k+1\).

Hence there is a component \(K\subseteq T\). Its size is at least \(k-3\), so at most three ports remain outside \(K\). There is exactly one other component \(D\) because each other component requires at least two ports. If \(D\) has three ports, then \(|K|=k-3\) and \(|T|=k\). The degree bound forces \(K\) to be a clique complete to all four anchors. Since \(T\) exhausts the even budget at \(z\), no remotes are at distance four or greater. All remotes lie in \(D\) at distance three from \(z\), and each touches at least one of the three ports of \(D\).

## Counting private remotes

Write \(P\) for these three ports and \(C\) for the set of remotes. For \(p\in P\), let \(C_p=N(p)\cap C\), and let \(B_p\) be the remotes at distance two from \(p\). Since \(|V(G)|\ge3k+3\),

\[
|C|=|V(G)|-k-5\ge2k-2>k.
\]

An anchor touching \(p\) sees all of \(C_p\) at distance two, so \(|C_p|\le k\). In case of equality, the anchor cannot miss another anchor, since any missed anchor would lie at distance two via \(z\). It must then touch every other port: if it missed one, that port could be reached in two steps through an adjacent anchor touching it. The chosen anchor would therefore see all of \(C\) at distance two, contradicting \(|C|>k\). It follows that \(|C_p|\le k-1\) for each port.

Every port already sees \(z\) and all of \(K\) at distance two, using \(k-2\) slots. Thus \(|B_p|\le2\). A private remote \(x\), one having only a single port neighbor \(p\), needs a neighbor outside \(C_p\) because \(|C_p|\le k-1\). Such a neighbor belongs to \(C_q\) for some other port \(q\), so \(x\in B_q\). Consequently there are at most six private remotes, and all other remotes are counted at least twice in \(\sum_{p\in P}|C_p|\). Therefore

\[
3(k-1)\ge\sum_{p\in P}|C_p|\ge2|C|-6\ge4k-10.
\]

This already excludes every \(k\ge8\).

## The remaining degrees

Let \(a\) count private remotes, and \(t\) count remotes adjacent to all three ports. An unordered pair of ports at distance two uses one of the remaining two even slots at each endpoint. If \(e\) counts those pairs, the preceding argument gives

\[
k-1+t\le a\le \sum_{p\in P}|B_p|\le 6-2e.
\]

The lower bound uses \(\sum_p|C_p|=2|C|-a+t\), \(|C|\ge2k-2\), and \(|C_p|\le k-1\). In particular \(a\ge4\). A pair of ports sharing a remote is either adjacent or at distance two.

If the ports form a triangle, each private remote is at distance two from both other ports, yielding \(2a\le6\), impossible. If the ports induce a two-edge path, the middle port sees all private remotes of the two ends at distance two, so there are at most two of these in total. Either end sees the opposite end at distance two and thus has at most one remaining slot for a private remote of the middle. Therefore \(a\le3\), also impossible.

Suppose the sole port edge is \(pq\), and write \(r\) for the isolated port. Every private remote of \(p\) belongs to \(B_q\) via the port edge, and conversely. Every private remote of \(r\) must lie in \(B_p\) or \(B_q\) by the outside-neighbor argument. Thus \(a\le |B_p|+|B_q|\le4\). Equality is required, which forces \(k=5\), \(a=4\), and \(t=0\). Neither \(p\) nor \(q\) can be at distance two from \(r\), since otherwise the two distance-two sets would have combined capacity at most three. All nonprivate remotes consequently see exactly the pair \(p,q\). There are at least four of them, and \(|C_p|,|C_q|\le4\), so there are exactly four and every private remote belongs exclusively to \(r\). Each private remote needs an outside neighbor, and the only outside remotes are the four shared by \(p,q\). Thus every private remote belongs to both \(B_p\) and \(B_q\), contradicting either bound of two.

Finally suppose the ports have no edges. Some remote is nonprivate, since \(|C|\ge8\) and \(a\le6\), and it puts one pair of ports at distance two. The displayed inequality and \(a\ge4\) now force \(e=1\), \(k=5\), \(a=4\), and \(t=0\). All nonprivate remotes see the unique distance-two pair, say \(p,q\). The same count then gives four such remotes filling \(C_p,C_q\), with all four private remotes belonging exclusively to the third port. Each private remote has to see one of the shared remotes, placing it in both \(B_p\) and \(B_q\) and giving the same contradiction.

Thus the three-port case is excluded for every \(k\ge5\). The final three-port case split incorporates the independent tightcover analysis.

## A portable saturated-layer inequality

For a root of degree \(d\), suppose a pure component has the least possible size \(k-d+1\) and the root has \(|T|=k\). The pure component is complete to all anchors. Let \(P\) be the other ports and \(C\) the remotes, all at distance three from the root. If \(|C|>k\), the same saturated-anchor argument gives \(|C_p|\le k-1\) for each \(p\in P\). Every port sees the root and the pure component at distance two. Hence if \(s=|P|\), if \(e_2(P)\) counts the unordered pairs of ports at distance two, and if \(r_i\) counts remotes with exactly \(i\) port neighbors, the outside-neighbor argument gives

\[
r_1\le s(d-2)-2e_2(P).
\]

Combining this with \(\sum_p|C_p|\le s(k-1)\) yields

\[
2|C|+\sum_{i\ge3}(i-2)r_i+2e_2(P)\le s(k+d-3).
\]

The inequality permits more than one other component. Separately, when every component contains a remote and every pair of high vertices has distance at most four, the opposite-remote count gives \(|V(G)|\le3k+d-3\).
