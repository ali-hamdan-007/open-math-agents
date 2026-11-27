# A degree-four root with a pure component and two outside ports

Let \(G\) be a finite 2-connected simple graph, let \(z\) have degree four, and suppose every vertex other than \(z\) has degree at least \(k\ge5\). Suppose each vertex has at most \(k\) vertices at positive even distance. Write \(A=N(z)\) and \(T=N_2(z)\). Assume \(|V(G)|>3k\) and that \(G-N[z]\) is disconnected with some component \(K\) contained in \(T\). If there are just two vertices of \(T\) outside \(K\), then \(G\) has a Hamilton path.

Call a vertex of a component of \(G-N[z]\) a port if it is in \(T\), equivalently if it has a neighbor in \(A\). Every such component has at least two ports and at least two distinct neighbors in \(A\). A single port or a single outside neighbor could be deleted to separate that component from the rest of \(G\). For the two-port statement, deleting the single port also needs another vertex to stay in the component. This is automatic here because the degree bound gives at least \(k-3\ge2\) vertices in every component, as each vertex has at most four neighbors outside it.

Thus there is just one other component \(D\), with ports \(u,v\), and

\[
k-3\le |K|\le k-2.
\]

The lower bound uses the degree bound in \(K\). The upper bound follows from \(|T|\le k\) and the two ports outside \(K\). When \(|K|=k-3\), every vertex of \(K\) sees all other vertices of \(K\) and all four anchors, since it has exactly \(k\) possible neighbors. When \(|K|=k-2\), every vertex of \(K\) misses at most one of its possible neighbors in \(K\cup A\).

## The large component

There is at most one vertex \(f\) at distance four from \(z\): the \(|K|+2\) vertices of \(T\) already use that many of its even slots. If \(|K|=k-2\), there is no such vertex, since \(|T|=k\). There is no vertex at distance at least five. If there were one, the fourth distance layer would separate it from \(z\), contradicting 2-connectivity because that layer has at most one vertex. All other nonports of \(D\) are at distance three from \(z\) and see at least one of \(u,v\). Let \(R\) be this set of distance-three vertices, and put \(R_u=N(u)\cap R\), \(R_v=N(v)\cap R\). Thus \(R=R_u\cup R_v\).

If an anchor touched both ports, it would see every vertex of \(R\) at distance two, giving \(|R|\le k\). With either value of \(|K|\) and the corresponding allowance for \(f\), this would give \(|V(G)|\le 2k+5\le3k\). Therefore the nonempty anchor-neighbor sets of \(u,v\) are disjoint.

For an anchor \(a\) touching \(u\), all of \(R_u\) are at distance two from \(a\). If \(a\) misses some other anchor, that anchor provides an additional witness via \(z\). Otherwise \(a\) sees the other port \(v\) at distance two via an anchor touching \(v\), since \(a\) is complete to the other anchors and does not touch \(v\). Applying the same reasoning at an anchor touching \(v\) gives

\[
|R_u|,|R_v|\le k-1,\qquad |R|\le2k-2.
\]

### When \(|D|\le2k\)

For clarity, the closure facts used here are elementary. In an \(N\)-vertex graph, one can add a missing edge \(xy\) with degree sum at least \(N\) without changing Hamilton-cycle existence. If a Hamilton cycle in the enlarged graph uses \(xy\), removing that edge gives the original path \(x=v_1,\ldots,v_N=y\). Among indices \(1\le i<N\), the index sets defined by \(xv_{i+1}\) and \(yv_i\) have combined size at least \(N\). They overlap, and at an overlap the two edges close the path after reversing its second segment. Adjoining a universal vertex gives the corresponding Hamilton-path closure threshold \(N-1\).

To \(D\) add a marker \(b\) adjacent only to \(u,v\). The path-closure threshold is \(|D|\). Each nonport of \(D\) has at least \(k\) neighbors inside \(D\), so closure can make the nonports into a clique. Each of \(u,v\) has a nonport neighbor, since deleting the other port from \(G\) must leave the nonports connected to the outside. Their nonport neighbor sets have union of size at least two: otherwise deleting their sole common neighbor would separate the remaining nonports from the outside. Here \(|D|-2\ge2\), since \(|V(G)|>3k\), \(|K|\le k-2\) and \(k\ge5\). Choose distinct nonports \(x\) and \(y\) touched by \(u\) and \(v\) respectively. The closure has a spanning path starting \(b,u,x\), traversing the nonport clique to \(y\), and ending at \(v\). Reversing the closure steps shows that the original marked graph has a spanning path.

### When \(|D|=2k+1\)

The bounds only allow this order if \(f\) exists, \(|K|=k-3\), and \(R_u,R_v\) are disjoint sets of size \(k-1\). The degree of \(f\) is at least \(k\) and all its neighbors belong to \(R\), so it sees at least one vertex in each group. Each port sees \(z\), all of \(K\), and \(f\) at distance two. These are \(k-1\) witnesses. There is no edge \(uv\), because it would put all \(k-1\) vertices of the opposite group at distance two from the port as well. Every cross edge between \(R_u\) and \(R_v\) puts its two ends at distance two from the opposite ports. Since each port has only one even slot left, there is at most one cross edge.

Every vertex of \(R_u\) that has no cross edge must be adjacent to all \(k-2\) other vertices of \(R_u\) and to \(f\), in addition to \(u\), to reach degree \(k\). The same holds for \(R_v\). There is at most one exceptional vertex per group, so each group is a clique. Thus \(D\) has a spanning path from \(u\) through the first clique to \(f\), then through the second clique to \(v\). Prepending \(b\) gives a spanning path of the marked graph in this case as well.

## Routing through the remaining vertices

The remaining graph, called the shell here, is the induced graph on \(A\cup\{z\}\cup K\). It has a spanning path joining any two prescribed distinct anchors \(a_1,a_2\). Write \(a_3,a_4\) for the other two anchors.

If \(|K|=k-3\), the clique \(K\) has at least two vertices and is complete to \(A\). Take the path

\[
a_1,z,a_3,x,a_4,\ (K\setminus\{x\}\text{ in any order}),\ a_2,
\]

where \(x\in K\).

If \(|K|=k-2\), add another marker to the shell adjacent only to \(a_1,a_2\). This auxiliary graph has \(k+4\) vertices, and each vertex of \(K\) still has degree at least \(k\). Cycle closure makes \(K\) a clique, since \(2k\ge k+4\). A spanning path between \(a_1,a_2\) in the closed shell gives a Hamilton cycle with the marker. Reversing cycle closure and removing that marker then gives the desired path in the original shell. All anchor-to-\(K\) adjacencies stay as they were.

First suppose every anchor has a neighbor in \(K\). Use the anchor pairs \((a_1,a_3)\) and \((a_4,a_2)\), with the path between the two corresponding clique segments going through \(a_3,z,a_4\). Let \(I,J\) be the common-neighbor subsets in \(K\) of these two anchor pairs. If \(I\) is empty, the first pair has nonempty disjoint neighbor sets and every vertex of \(K\) sees both anchors of the second pair, because each vertex misses at most one anchor. Use one vertex from each first-pair neighbor set to make the first clique segment. Route all remaining clique vertices between the anchors of the second pair. There is at least one remaining vertex since \(|K|=k-2\ge3\). If \(J\) is empty, use the symmetric construction. If \(I,J\) are both nonempty, they contain distinct representatives \(x,y\). Otherwise both are the same singleton and any different vertex of \(K\) would miss one anchor from each pair, a contradiction. Assign \(x\) to the first segment and \(y\) to the second. If there are unassigned vertices, take any one of them as the other endpoint of the first clique segment and route all the unassigned vertices through that segment. The chosen vertex sees at least one anchor of the first pair and \(x\) sees both, so this segment has the required two anchor edges.

Finally suppose some anchor \(a\) has no neighbor in \(K\). Every vertex of \(K\) sees the other three anchors. Since the port anchor-neighbor sets are disjoint, \(a\) has at most one neighbor in \(D\). Its only possible neighbors are then \(z\), the other three anchors, and that port. Its degree is at least \(k\ge5\), so this can only occur at \(k=5\), when it sees all the other anchors. If \(a=a_1\), use \(a_1,a_3,z,a_4,K\ldots,a_2\); if \(a=a_2\), reverse the corresponding route. If \(a\) is one of the interior anchors, call the other one \(c\) and use \(a_1,K\ldots,c,z,a,a_2\). This also handles the smallest clique size in this case.

## Expanding the marker

Take any spanning path of \(D+b\) supplied above. If \(b\) is internal, its two neighbors on the path are \(u,v\). Choose distinct anchors touched by \(u,v\) respectively, which is possible because their anchor sets are nonempty and disjoint. Replace \(b\) by the shell path between those anchors. If \(b\) is an endpoint next to a port, choose any anchor touched by that port and use a shell path ending at that anchor, beginning at another anchor. In both cases the resulting path spans \(G\).

This proves the stated two-port case directly from the even-distance cap and 2-connectivity, without a separate upper order bound.
