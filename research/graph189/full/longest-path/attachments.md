# Omitted components of longest paths and the order bound \(n\leq 3k+2\)

Let \(G\) be a finite simple graph. Write \(k\geq3\) for its second-smallest degree and \(\delta\) for its least degree. A vertex is called high if its degree is at least \(k\). All vertices except a possible unique vertex \(z\) are high. Assume each vertex has at most \(k\) vertices at distance exactly two. The full even-distance hypothesis of Graph Conjecture 189 implies this assumption. The results below use only the distance-two bound.

## Longest-path attachment count

Let \(P=(p_1,\ldots,p_l)\) be a longest path. We also consider the version where \(P\) is longest among paths containing a prescribed vertex \(w\). For each omitted vertex \(x\), let
\[
 A_x=\{i:p_i\sim x\},\quad a_x=|A_x|,\quad q_x=|N(x)\setminus V(P)|.
\]
Every attachment index is internal to \(P\), and no two consecutive indices are in \(A_x\). Otherwise extending at an endpoint or inserting \(x\) in a path edge would give a longer path, preserving \(w\) when applicable.

Partition \(A_x\) into its maximal runs with successive indices differing by two. Write \(r_x\) for the number of runs, with \(r_x=0\) if \(A_x\) is empty. The union \(B_x=(A_x-1)\cup(A_x+1)\) has size \(a_x+r_x\). A run of size \(j\) has \(j+1\) shifted indices, and shifted indices from distinct runs are disjoint since a shared shifted index would join the runs. For every \(i\in B_x\), \(p_i\) is nonadjacent to \(x\) and at distance two from it by way of an original attachment. Thus \(a_x+r_x\leq k\). In particular every omitted high vertex has \(q_x\geq1\): otherwise \(a_x\geq k\), \(r_x\geq1\) would violate the bound.

Suppose omitted vertices \(x,y\) are adjacent. Their attachment sets have no pair of indices differing by one, because the pair \(x,y\) could be inserted between those path vertices. Their attachment sets have no pair of indices differing by two in the unrooted version: replacing the middle path vertex by \(x,y\) gives a longer path. In the rooted version, a pair differing by two is possible only if the middle path vertex is \(w\). The splice can be read in either direction, depending on the order of the attachment indices.

In particular, \(A_y\setminus A_x\) is disjoint from \(B_x\) and supplies extra distance-two witnesses from \(x\) via \(y\). We obtain
\[
 k\geq a_x+r_x+a_y-|A_x\cap A_y|. \tag{1}
\]
If \(A_x\) has a nonsingleton run, an overlapping attachment index in this run would have another \(A_x\)-index at distance two. In the unrooted version this is impossible, so \(|A_x\cap A_y|\leq r_x-1\) and \(a_x+a_y\leq k-1\). In the rooted version only the run that contains the positions immediately before and after \(w\) could contribute an overlapping index from a nonsingleton run. That run contributes at most two, and all singleton runs contribute at most one each. Consequently \(|A_x\cap A_y|\leq r_x+1\) and \(a_x+a_y\leq k+1\).

## Size of an omitted component

**Unrooted statement.** If \(G\) is 2-connected, every component of \(G-V(P)\) is either the singleton low vertex or has at least \(\lceil k/2\rceil+1\) vertices.

Suppose first that such a component has size \(m\leq\lceil k/2\rceil\) and contains an adjacent high pair \(x,y\). For either vertex, \(a_x\geq k-m+1\), so \(a_x>k/2\). The bound \(a_x+r_x\leq k\) therefore forces a nonsingleton run. The inequality \(a_x+a_y\leq k-1\) contradicts \(a_x+a_y>k\).

If the component has high vertices and contains no adjacent high pair, it must have the unique low vertex as the center of a star, because every omitted high vertex has an omitted neighbor. A high leaf \(x\) has \(q_x=1\), so \(a_x=k-1\), \(r_x=1\), and \(B_x\) exhausts the distance-two budget. Another leaf would itself be one more distance-two witness via the center. Thus the component consists of one high vertex \(x\) and the low center \(z\). By (1) and saturation, \(A_z\subseteq A_x\). Since \(k-1\geq2\), each index of the single run \(A_x\) has another index of that run at distance two. The pair splice would lengthen \(P\) if \(z\) had any attachment. Thus \(z\) has no attachment and its only neighbor is \(x\), contrary to 2-connectivity.

When \(k=2h\), an omitted component of order exactly \(h+1\) containing high vertices must be a clique. Indeed the preceding star argument still excludes the absence of a high-high edge. If \(x,y\) is a high-high edge, their attachment orders are at least \(h\). Neither can have a nonsingleton run, for then \(a_x+a_y\leq 2h-1\). Thus both have exactly \(h\) attachments, are adjacent to all other component vertices, and this immediately gives every other high vertex a high neighbor. This establishes that all high vertices are universal in the component and therefore the whole component is a clique. For each high \(x\), \(B_x\) uses the full budget, and (1) forces all high vertices to share the same attachment set. Distinct common attachment indices are at least \(h+2\) apart on \(P\); a closer pair permits replacing the intervening segment by a spanning path of the \((h+1)\)-clique. This separation also applies between a low component vertex's attachments and any common high attachment index.

**Rooted statement.** If \(P\) is longest through \(w\) and all omitted vertices are high, every omitted component has order at least \(\lfloor k/2\rfloor+1\).

A singleton is impossible. In a component of size \(2\leq m\leq\lfloor k/2\rfloor\), take any edge \(xy\). Then \(a_x,a_y\geq k-m+1\) and \(a_x+a_y\geq k+2\). Again \(a_x>k/2\) forces a nonsingleton run, and the rooted bound \(a_x+a_y\leq k+1\) contradicts this. This statement does not use 2-connectivity.

## Almost-spanning paths

Assume \(G\) is 2-connected and is not traceable. If a path covers at least \(n-\lceil k/2\rceil\) vertices, a longest path omits only the singleton low vertex \(z\), by the unrooted statement. In particular it omits neither exactly two vertices nor a unique high vertex. All other vertices are high, and \(d(z)=\delta\geq2\).

Given any two attachment indices of \(z\) on a longest path, let \(g\) be their difference. Replacing the \(g-1\) intervening vertices by \(z\) gives a path through \(z\) omitting \(g-1\) high vertices. A longest path through \(z\) omits no more than \(g-1\) and, since \(G\) is not traceable, omits at least \(\lfloor k/2\rfloor+1\). It follows that \(g\geq\lfloor k/2\rfloor+2\). The \(\delta\) attachments are internal to an \((n-1)\)-vertex path, so
\[
 n\geq (\delta-1)(\lfloor k/2\rfloor+2)+4. \tag{2}
\]
The gaps are at least three, so the two shifts of each attachment index are all distinct. They give \(2\delta\) vertices at distance two from \(z\), proving \(2\delta\leq k\).

## The cone is 1-tough when \(n\leq3k+2\) and \(k\geq7\)

Assume \(G\) is 2-connected, \(n\leq3k+2\), and \(k\geq7\). Choose a least-degree vertex \(z\) even when all vertices are high, and put \(X=V(G)\setminus\{z\}\). Then \(\alpha(G[X])\leq k+2\). In an independent set of size \(k+3\), one vertex would have another member at distance at least three by its distance-two cap. Their neighborhoods are disjoint from one another and from the independent set. Both degrees are at least \(k\), requiring at least \(3k+3\) vertices.

Let \(H\) be the cone obtained by adding a universal vertex to \(G\). Any cut of \(H\) leaving at least two components includes the universal vertex. Thus a failure of 1-toughness gives a set \(S\subseteq V(G)\) with \(s=|S|\), and \(t\geq s+2\) components in \(G-S\). Since \(G\) is 2-connected, \(s\geq2\). Every component meeting \(X\) has size at least \(k-s+1\), since a vertex of \(X\) in it has at most \(s\) neighbors outside the component. Every component has neighbors in at least two distinct vertices of \(S\), because a unique such vertex would be a cut vertex of \(G\). If a component of order at least two has only one of its own vertices touching \(S\), this vertex would likewise be a cut vertex. So a nonsingleton component has at least two vertices that touch \(S\).

Suppose all components meet \(X\). Choosing representatives in \(X\) shows \(t\leq k+2\), so \(s\leq k\).

- For \(2\leq s\leq k-2\), the order satisfies \(n\geq s+(s+2)(k-s+1)\geq4k-2\). The latter inequality follows by concavity in \(s\) and evaluating both ends. This exceeds \(3k+2\).
- For \(s=k-1\), at most one vertex is available in excess of \(k+1\) components of size two. At least two such components consist entirely of \(X\)-vertices. Each of those vertices is adjacent to every member of \(S\). From one such vertex, every other component contributes a distinct distance-two witness through \(S\), and the second such pair contributes two. This exceeds \(k\).
- For \(s=k\), there are exactly \(k+2\) components with at most \(2k+2\) vertices in total. There is a singleton of \(X\), whose vertex sees all of \(S\) and at least one vertex in every other component at distance two. This gives \(k+1\) witnesses.

Otherwise a component is the singleton \(z\), and all other components meet \(X\). Thus \(t-1\leq k+2\) and \(s\leq k+1\).

- For \(3\leq s\leq k-2\), \(n\geq 1+s+(s+1)(k-s+1)\geq4k-4\) by concavity; this exceeds \(3k+2\).
- For \(s=k-1\), at most two vertices are available in excess of \(k\) pairs and \(z\). There are at least two \(X\)-pairs, each entirely adjacent to \(S\). From a vertex in one pair, all \(t-1\geq k\) other components contribute at least one distance-two witness and the other pair gives a second one.
- For \(s=k\) or \(s=k+1\), at least \(s+1\) components lie in \(X\), on at most \(3k+1-s<2(s+1)\) vertices. Thus one is an \(X\)-singleton. Its vertex sees all but at most one member of \(S\). Every other component has at least two distinct neighbors in \(S\), so contributes a distance-two witness through a shared neighbor. There are at least \(k+1\) such components.
- For \(s=2\), there are exactly three \(X\)-components. Their minimum sizes \(k-1\) leave at most two extra vertices, so one has size \(k-1\), all of whose vertices see both members of \(S\). At least one other \(X\)-component has size at most \(k\), so every vertex of it sees \(S\), contributing at least \(k-1\) witnesses to the distance-two set of a vertex in the minimum component. The third \(X\)-component contributes at least two of its vertices touching \(S\), and \(z\) contributes one. This gives at least \(k+2\) witnesses.

This proves 1-toughness of \(H\).

## Consequence using Li's subset circumference theorem

For \(k\geq7\) and \(n\leq3k+2\), let \(G\), \(X\), and \(H\) be as above. Suppose \(X\) contains an independent triple in \(H\). Each member of \(X\) has ambient degree at least \(k+1\) in \(H\). Therefore the minimum ambient degree sum \(\sigma_3^H(X)\) of an independent triple from \(X\) is at least \(3(k+1)\geq n+1=|V(H)|\). Jianping Li's Theorem 8, for a 1-tough graph with this ambient degree-sum threshold, gives a cycle containing at least
\[
 \min\bigl\{|X|,\ |X|+\tfrac13\sigma_3^H(X)-\alpha(H[X])\bigr\}
 \ \geq\ |X|-1
\]
vertices of \(X\). Remove the universal vertex if the cycle contains it, or delete one cycle edge if it omits the universal vertex. The resulting path in \(G\) covers at least \(n-2\) vertices.

If \(X\) has no independent triple, then \(\alpha(H)\leq3\). The cone is 3-connected because \(G\) is 2-connected. The Chvátal–Erdős theorem supplies a Hamilton cycle in \(H\), giving a spanning path in \(G\).

The almost-spanning conclusion proves that \(G\) is traceable whenever \(2\delta>k\) or \(n<(\delta-1)(\lfloor k/2\rfloor+2)+4\). In particular \(\delta\geq7\) suffices throughout \(n\leq3k+2\), since the right side of (2) is at least \(3k+13\). The distance-two hypothesis alone suffices for the 2-connected version stated here. For the full Graph Conjecture 189 hypothesis, non-2-connected graphs are separately covered by Easwar–Johari, Theorem B. The \(3k+2\) traceability extension here applies for \(k\geq7\).

### References

- Jianping Li, “Cycles Containing Many Vertices of Subsets in 1-Tough Graphs with Large Degree Sums,” *Ars Combinatoria* 48 (1998), 195–212, Theorem 8, pp. 196–197. [PDF](https://combinatorialpress.com/article/ars/Volume%20048/volume-48-paper-18.pdf)
- R. Easwar and S. Johari, “Conditions for traceability under a bound on the size of even-distance sets,” Theorem B. [Preprint](https://arxiv.org/abs/2609.11719)
- Chvátal–Erdős Hamiltonicity criterion: a graph with at least three vertices and connectivity at least its independence number is Hamiltonian.
