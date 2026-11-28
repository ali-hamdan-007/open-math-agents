# Cone factor barriers at small connectivity

Let \(G\) satisfy Graph 189, have second-smallest degree \(k\ge11\) and vertex connectivity at least two. Adjoin a universal vertex \(z\) to form \(G^+\) and set \(C=\min(10,\lfloor(k-1)/6\rfloor)\). If \(G^+\) has no 2-factor, every biased Tutte barrier has \(z\) in its first set and at least \(k+C+1\) original vertices there. The cone has a 2-factor whenever \(n\le5k\). These restrictions apply also at connectivity two, three and four.

The argument uses the notation and canonical incidence properties of [the earlier barrier bound](cone-barrier-size.md). Removing \(z\) from the first barrier set leaves sets \(S,T,U\) partitioning \(V(G)\), with \(s=|S|\), \(t=|T|\), and \(E\) edges between \(T\) and \(U\). The deficiency inequality is

\[
t\ge s+2,\qquad q\ge E-2(t-s-2),
\]

where \(q\) counts the components of \(G[U]\) incident with an odd number of \(T\) edges. The other components have no \(T\) edges. Each vertex of \(U\) meets at most one member of \(T\), and every member of \(T\) has at most one neighbor per component of \(G[U]\). As in the earlier bound, all but at most one member of \(T\) are high and have only high neighbors in \(U\). Call these members good. We write \(b_v\) for the number of \(U\) neighbors of \(v\in T\).

## Extending the known bound to connectivity two

The earlier proof puts \(z\) in the first set and excludes \(s\le k\). Only its final case uses the assumption of connectivity at least five. There \(s=k\) and a good \(v_0\in T\) has no neighbor in \(U\), so it is adjacent to every anchor in \(S\). Keep its notation \(a=|\{v\in T:N(v)\cap S\ne\varnothing\}|\), \(w=t-a\), and \(p=|\{u\in U:N(u)\cap S\ne\varnothing\}|\). We have \(a-1+p\le k\). The case in which every anchor-free vertex is low is ruled out there by connectivity at least two. Otherwise \(q\ge k\) because a high anchor-free vertex has at least \(k\) contacts in distinct odd components.

Each odd component missing all \(S\)-contacts has at least two distinct boundary vertices by connectivity, all in \(T\). Its odd number of \(T\) edges is therefore at least three. Thus \((E-q)/2\ge q-p\). It follows that

\[
t\ge k+2+q-p\ge k+a+1,\qquad w\ge k+1 .
\]

Since \(E\ge k(w-1)\), the earlier order inequality gives \(n\ge2k+4-a+(k-1)w\ge k^2+k+2\). This exceeds the quadratic ceiling \(1+2k+\lfloor(k+1)^2/4\rfloor\). No larger-connectivity hypothesis is required.

## First sets of size \(k+c\) when all good vertices meet \(U\)

Write \(s=k+c\), with \(c\ge1\), and put \(D=\lfloor s/2\rfloor\). Call a good member of \(T\) dense if it has more than \(s/2\) neighbors in \(S\). Let \(h\) count these dense vertices. They see each other at distance two.

If \(h\ge\lceil s/2\rceil+2\), a dense vertex already sees \(h-1\) dense peers. Every \(U\) neighbor of that dense vertex is high, and each of its internal neighbors in its own component of \(G[U]\) gives a further distance-two witness. Thus such a contact has internal degree at most \(k-h+1\), and has at least \(k-1-(k-h+1)=h-2\ge\lceil s/2\rceil\) neighbors in \(S\). This support meets every dense support, since their sizes add to more than \(s\). Each dense vertex therefore sees another \(h-1\) witnesses by taking one \(U\) contact of each other dense vertex. The contacts are distinct and none is adjacent to the root by the canonical incidence rule. Since \(2(h-1)>k\), we obtain \(h\le\lceil s/2\rceil+1\).

Each good nondense vertex needs at least \(d=k-D\) neighbors in \(U\), and each dense vertex has at least one. Hence

\[
q\ge(d-2)(t-h-1)+2s+2-h.
\]

When \(D\le k-1\), add \(s+t\) to the bound for \(q\). The result is nondecreasing in \(t\) and nonincreasing in \(h\). Substituting \(t=s+2\) and \(h=\lceil s/2\rceil+1\) gives

\[
n\ge D(k-D-1)+3s+3.
\]

If \(1\le c\le10\) and \(k>6c\), then \(D\le k-1\) and this exceeds the quadratic ceiling. Writing \(\epsilon=s\bmod2\), the difference from \(1+2k+(k+1)^2/4\) is

\[
3c+2-\frac{(c+1-\epsilon)^2}{4}>0.
\]

## First sets of size \(k+c\) when a good vertex misses \(U\)

Let \(v_0\in T\) be good with \(b_{v_0}=0\), and write \(Q=N(v_0)\subseteq S\), so \(|S\setminus Q|\le c\). Let \(a\) count the members of \(T\) with a neighbor in \(Q\), and let \(p\) count the vertices of \(U\) with a neighbor in \(Q\). The quota at \(v_0\) gives \(a-1+p\le k\). As \(t\ge k+c+2\), there are at least two vertices in \(T\) without a neighbor in \(Q\), including a high one. Such a high vertex has at least \(k-c\) neighbors in \(U\), in distinct odd components. Hence \(q\ge k-c\).

An odd component with no contact to \(Q\) has at least three \(T\) edges, except possibly if it has one \(T\) edge and attaches to some anchor \(u\in S\setminus Q\). This is the only other way to have at least two distinct boundary vertices. If \(k>6c\), at most two exceptions per such anchor have a high \(u\)-neighbor. Indeed, if three such components \(C_i\) have high \(u\)-neighbors \(y_i\), write \(A_i=N(u)\cap C_i\). Root \(y_i\) sees all members of the other two \(A_j\) at distance two, so \(2\sum_i|A_i|\le3k\). Every \(y_i\) has at most \(c+1\) external neighbors, so its closed internal neighborhood has size at least \(k-c\). These closed internal neighborhoods lie in the union of the \(A_i\) and the distance-two set of \(u\). Consequently \(3(k-c)\le3k/2+k\), which implies \(k\le6c\). At most one more exception has only the low vertex as its contact to \(S\setminus Q\).

At most \(p\) odd components have a contact to \(Q\). Thus \((E-q)/2\ge q-p-(2c+1)\), and the deficiency yields

\[
t\ge k+c+2+q-p-(2c+1)\ge k+a-2c .
\]

Put \(w=t-a\ge k-2c\). A high member of \(T\) without a \(Q\)-neighbor has at least \(k-c\) neighbors in \(U\), so \(E\ge(k-c)(w-1)\). The order then satisfies

\[
\begin{aligned}
n&\ge s+t+q\ge3s+4-t+E\\
 &\ge3k+3c+4-a-w+(k-c)(w-1)\\
 &\ge k^2-3ck+2c^2+6c+3 .
\end{aligned}
\]

The last expression exceeds \(1+2k+(k+1)^2/4\) when \(k>6c\) and \(c\ge1\). Four times the difference is \(3k^2-(12c+10)k+8c^2+24c+7\), which is \(4c(11c-3)>0\) at \(k=6c+1\) and increases for larger \(k\).

## The cone has a 2-factor through order \(5k\)

Suppose \(n\le5k\). An independent set of high vertices has size at most \(2k\). Indeed, if its size exceeds \(2k\), the [disjoint-support packing inequality](disjoint-support-packing.md) requires at least three pairwise disjoint neighborhoods, each of size at least \(k\) and disjoint from the independent set. Then \(n\ge5k+1\). Since at most one member of \(T\) is low, this gives \(t\le2k+1\) and \(s\le2k-1\). By the barrier-size result write \(s=k+c\) with \(2\le c\le k-1\).

If every good vertex meets \(U\), the dense-count bound gives

\[
n\ge D(k-D-1)+3s+3\ge D(k-D+5)+3 .
\]

The last polynomial is concave in \(D\), so its minimum on \(\lfloor(k+1)/2\rfloor\le D\le k-1\) is attained at an endpoint. At \(D=k-1\) it is \(6k-3>5k\). At the left endpoint, write \(k=2d\) or \(k=2d+1\). The differences from \(5k\) are respectively \(d^2-5d+3\) and \(d^2-4d+3\), both positive in the stated range.

Otherwise take the good root \(v_0\) with \(b_{v_0}=0\), retaining its neighborhood \(Q\) and the counts \(a,p\) from the preceding section. Set \(\eta=t-s-2\ge0\) and \(b=k+1-a\ge p\). Then \(w=t-a=c+1+\eta+b\). Every high member of \(T\) avoiding \(Q\) has at least \(k-c\) neighbors in \(U\), so

\[
E\ge(c+\eta+b)(k-c).
\]

Every vertex of \(U\) has at most one neighbor in \(T\), so \(E\le |U|\) and

\[
n\ge 2s+2+\eta+(c+\eta+b)(k-c).
\]

If \(c\in\{2,3\}\), this bound forces \(\eta=0\) and \(b\le1\). At \(c=2\), setting \(\eta=1\) gives \(5k+1\) and setting \(b=2\) gives \(6k-2\). At \(c=3\), either \(\eta=1\) or \(b=1\) already gives more than \(5k\). Thus \(q=E\ge c(k-c)\), and every odd component has exactly one \(T\) edge. Since \(|U|\le3k-2c-2\), at least \(2q-|U|\ge k-2\) of the odd components are singletons. At most one singleton is low and at most \(p\le1\) have a neighbor in \(Q\). Any other singleton has degree at most \(c+1<k\), a contradiction.

For \(c\ge4\) the order inequality implies \(n\ge2k+2+c(k-c+2)\). If \(4\le c\le k-2\), the concave polynomial \(c(k-c+2)\) is at least \(4(k-2)\), its value at both endpoints. This gives \(n\ge6k-6>5k\). Thus \(c=k-1\), so \(s=2k-1\) and \(t=2k+1\), with \(|U|\le k\) and \(q=E\). The bound \(a\le k+1\) gives \(w\ge k\). Each of the at least \(k-1\) high vertices in \(T\) avoiding \(Q\) has at least one \(U\)-neighbor. Since \(E\le k\), at least \(k-2\) such high vertices have exactly one \(U\)-neighbor. Each then has all \(k-1\) anchors in \(S\setminus Q\) as neighbors, by its degree.

Also \(w\le E+1\le k+1\), so \(a\ge k\) and \(p\le1\). There are at least \(2q-|U|\ge k-2\) singleton odd components. At most one is low and at most one touches \(Q\). Each of the remaining at least \(k-4\) singletons has one \(T\)-neighbor and is adjacent to every anchor in \(S\setminus Q\), again by its degree. A high root among the \(k-2\) vertices chosen above sees at least \(k-3\) peers in its group and at least \(k-5\) of these singletons at distance two via \(S\setminus Q\), excluding its one direct \(U\)-neighbor. This supplies \(2k-8>k\) witnesses and completes the contradiction.

The argument is on paper. A 2-factor may have multiple cycles, and the larger canonical barriers remain open at general order.
