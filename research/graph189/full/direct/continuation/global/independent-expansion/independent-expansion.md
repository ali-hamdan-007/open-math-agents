# Independent-set expansion under the Graph 189 hypotheses

Let \(G\) be a connected graph satisfying Graph 189. Write \(k\) for the second entry of its degree list, \(n\) for its order, and \(\kappa\) for its vertex connectivity. A vertex is high if its degree is at least \(k\). There is at most one vertex that is not high, and two high vertices have distance at most four by the registered metric lemma.

For every integer \(g\ge0\), if \(\kappa\ge g+2\) and \(n\ge2k+g+3\), then every nonempty independent set \(I\) satisfies

\[
|N(I)|\ge |I|+g+1 .
\]

In particular, for \(\kappa\ge2\) and \(n\ge2k+3\), the surplus is at least \(\min(\kappa-1,n-2k-2)\). This applies also when \(I\) contains the unique low vertex.

## Proof

Suppose some nonempty independent set has surplus at most \(g\). Choose an inclusion-minimal such set \(J\), and put \(S=N(J)\), \(R=V(G)\setminus(J\cup S)\), \(m=|J|\) and \(s=|S|\). Thus \(s\le m+g\). Each vertex has degree at least \(\kappa\), so \(J\) cannot be a singleton and it contains a high vertex.

Take any high \(x\in J\), let \(Q=N(x)\), and let \(F\) be the members of \(J\) whose neighborhoods are disjoint from \(Q\). If \(F\) is nonempty, it is proper because \(x\notin F\). Minimality gives

\[
|F|\le |N(F)|-g-1\le s-|Q|-g-1 .
\]

Each member of \(J\setminus(F\cup\{x\})\) is at distance two from \(x\), so there are at least \(m-1-|F|\ge |Q|\ge k\) such vertices. Thus all \(k\) even places at \(x\) are spent on members of \(J\) at distance two. A high \(y\in F\) cannot be at distance three because the preceding vertex on a geodesic from \(x\) to \(y\) would lie in the independent set \(J\). Distance four is ruled out by the spent allowance, and a larger distance by the high-pair bound. Therefore all pairs of distinct high members of \(J\) share a neighbor, whether or not \(F\) is empty. There are at most \(k+1\) high members, so \(m\le k+2\).

Suppose the low vertex \(z\in J\) misses all neighbors of a high \(x\in J\). Because \(\deg(z)\ge\kappa\ge g+2\), disjointness gives \(s\ge k+g+2\). Combined with \(s\le m+g\le k+g+2\), this forces \(m=k+2\), \(s=k+g+2\), and \(\deg(z)=g+2\). Every high root spends all \(k\) slots on the other high members of \(J\), so no high root shares a neighbor with \(z\). Their neighborhoods all equal \(S\setminus N(z)\), a set of size \(k\). An edge from that common neighborhood to any vertex outside its union with \(J\setminus\{z\}\) would give an extra distance-two witness to a high root. Since none of the high roots has an edge outside that union either, the union disconnects from \(z\), a contradiction.

Thus any high \(x\in J\) sees all \(m-1\) other members of \(J\) at distance two. At most \(r=k-m+1\) vertices of \(R\) have a neighbor in \(Q=N(x)\), as each is another distance-two witness. Write \(B=N(Q)\cap R\). Deleting \((S\setminus Q)\cup B\) leaves \(J\cup Q\) without edges to \(R\setminus B\). This deletion has size at most

\[
(s-k)+r=s-m+1\le g+1<\kappa .
\]

It follows that \(R=B\), and

\[
n=m+s+|R|\le m+s+r=k+s+1\le2k+g+2 .
\]

Here \(m\le k+1\) follows from the allowance at \(x\), giving \(s\le k+1+g\). This contradicts the stipulated order and proves the expansion.

## Consequences for path obstructions

Write \(e=\min(\kappa-1,n-2k-2)\) in the range \(\kappa\ge2,n\ge2k+3\). If \(T\) is independent and \(S,T,U\) partition the graph, then at least \(|T|-|S|+e\) members of \(T\) have a neighbor in \(U\) whenever some member of \(T\) has no neighbor in \(U\). Indeed the unmarked members have neighborhood contained in \(S\), so they number at most \(|S|-e\). This excludes thin path-incidence barriers in which too few vertices of an oversized independent part have any exterior access.

After deleting any at most \(e\) vertices, the remaining graph has a spanning collection of disjoint cycles and edges. Its independent sets have at least as many neighbors as members, by subtracting the deletions from the neighborhood bound. This is sufficient for Hall's condition in the bipartite adjacency graph on two copies of the remaining vertex set. For any subset \(W\), the vertices of \(W\setminus N(W)\) are independent and have neighborhood inside \(N(W)\setminus W\), so \(|W|\le|N(W)|\). A perfect matching supplies an adjacency permutation whose cycles of length two are edges.

## Equality at high degree

For \(2\le\kappa<k\), take a \(k\)-clique \(S\), an independent set \(J\) of size \(k-\kappa+1\) completely joined to \(S\), and a \((k+\kappa)\)-clique \(R\). Join \(S\) completely to a \(\kappa\)-set \(Q\subset R\), with all other cross edges absent. The graph has order \(3k+1\), second-smallest degree \(k\), and connectivity \(\kappa\). Deleting \(Q\) disconnects it, and a smaller deletion leaves vertices in \(Q\) and in \(S\), which connect the surviving parts.

Each root in \(J,S,Q,R\setminus Q\) has respectively \(k,k,|J|,k\) other vertices at positive even distance. For a root in \(J\) these are the other members of \(J\) and all of \(Q\). For a root in \(S\) they are \(R\setminus Q\). The last two root classes see respectively \(J\) and \(S\) at distance two. The graph has a spanning path obtained by alternating all of \(J\) with members of \(S\), then visiting the remaining members of \(S\) and finally the clique \(R\) beginning in \(Q\). The independent set \(J\) attains surplus \(\kappa-1\), showing that an extra unit cannot be demanded uniformly in the high-degree residual range.

This is a paper proof with an independent finite replay. It does not establish traceability for an arbitrary qualifying graph.
