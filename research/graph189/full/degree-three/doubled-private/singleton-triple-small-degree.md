# Degree and connectivity bounds for the doubled-private triangle with one triple-visible remote

Retain the notation of the doubled-private triangle with \(T=\{t\}\). The private middle vertices are \(P,Q,B,C\), where \(P,Q\) share anchor \(A\). The common middle vertices form \(W\), of size \(k-4\). Write \(F\) for the induced nontriple remote layer. For a private \(J\), write \(R_J\) for its remote neighbors, \(H_J\) for their closed neighborhood in the full remote layer, \(a_J=|N(J)\cap W|\), and \(S_J=R_J\cap V(F)\). We assume \(n>3k\), the second-smallest degree is \(k\), the degree-three root has eccentricity at most three, and every vertex has at most \(k\) vertices at distance two.

The bounds in [solo-ports.md](solo-ports.md) and [two-cut.md](two-cut.md) give at least three solo remotes per private, \(a_P,a_Q\ge4\), \(a_B,a_C\ge2\), and \(|H_J|\le 2k-8\). Every common middle meets one or two privates, some common middle meets just one, and no common middle meets both \(B,C\). Each solo's closed neighborhood in the remote layer has size at least \(k\) and lies in \(H_J\). The external boundary of \(R_J\) in the remote layer has size at most \(a_J+1\). Consequently
\[
k\le |H_J|\le |S_J|+a_J+2.
\]

If a common middle has two private neighbors \(I,J\), it sees the root, both missed privates, and \(S_I\cup S_J\) at distance two. Thus \(|S_I\cup S_J|\le k-3\). This bounds each of \(|S_I|\) and \(|S_J|\) by \(k-6\), since the other set has at least three solos. In particular, a private in such a pair has \(a_J\ge4\). Two complementary pairs cannot occur, since the four supports together contain all at least \(2k-4\) nontriple remotes. If both \(B,C\) occur in pairs, their partners must therefore be the same twin, say \(P\). No two of \(Q,B,C\) can occur together, and all three have at least four common neighbors. Their common neighborhoods are disjoint, so \(|W|\ge12\) and \(k\ge16\).

If a common middle has only one private neighbor \(J\), its degree forces it to be adjacent to \(t\). It sees the root, the three missed privates, and \(S_J\cup (N(t)\cap V(F))\) at distance two. Hence
\[
|S_J\cup (N(t)\cap V(F))|\le k-4,\qquad
|(N(t)\cap V(F))\setminus S_J|\le a_J-2.
\]
Two saturation facts follow.

- If \(J\) occurs as a lone neighbor and \(a_J=2\), then \(|S_J|=k-4\), \(N(t)\cap V(F)\subseteq S_J\), and \(|H_J|=k\). The latter equality forces \(t\in R_J\). Each solo of \(J\) has its size-\(k\) closed remote neighborhood equal to \(H_J\), so \(t\) is adjacent to every \(J\)-solo. In particular, two distinct privates with \(a_J=2\) cannot both occur as lone neighbors.
- If \(J\) occurs in a pair and \(a_J=4\), then \(|S_J|\le k-6\) gives \(|H_J|=k\) and forces \(t\in R_J\). Again, \(t\) is adjacent to every solo of \(J\). Each of those at least three solos lies outside every other support; thus any other private occurring as a lone neighbor must have at least five common neighbors.

## The template requires \(k\ge14\)

The established bound \(k\ge11\) leaves \(k=11,12,13\) to exclude. We may suppose at most one singleton private occurs in a pair, by the bound \(k\ge16\) above. If neither singleton private occurs in a pair, they account for at least four common middles with a lone private neighbor. If only \(B\) occurs in a pair, \(C\) accounts for at least two. The total private-common incidence count equals twice \(|W|\) minus the number of common middles with a lone private neighbor. Thus the two cases require respectively \(12\le2(k-4)-4\) and \(14\le2(k-4)-2\), excluding \(k=11\).

For \(k=12\), the relevant incidence bound is an equality. In the case where neither singleton private occurs in a pair, we get \(a_C=2\), \(a_P=a_Q=4\), and four \(P,Q\) pairs. If only \(B\) occurs in a pair, we likewise have \(a_C=2\) and \(a_P=a_Q=4\). There are six pairs and \(a_B=4\), so a pair \(P,Q\) occurs. In both cases the second saturation fact applied to \(P\) contradicts the lone \(C\) with \(a_C=2\).

Take \(k=13\), so \(|W|=9\). First suppose neither singleton private occurs in a pair. If \(a_B,a_C\ge3\), there are at least six lone-neighbor common middles, yielding at most 12 incidences, whereas \(a_P+a_Q+a_B+a_C\ge14\). The first saturation fact excludes \(a_B=a_C=2\). In the remaining case one has two and the other at least three. There must be a pair, since otherwise there are only nine incidences. Every pair is \(P,Q\), so the second saturation fact requires \(a_P,a_Q\ge5\) because a singleton occurs as a lone neighbor with \(a_J=2\). At least five lone-neighbor common middles give at most 13 incidences, yet \(a_P+a_Q+a_B+a_C\ge15\).

Now suppose only \(B\) occurs in a pair. If \(a_C\ge3\), the lower bound \(12+a_C\) on incidences and upper bound \(18-a_C\) require \(a_C=3\) and \(a_P=a_Q=a_B=4\). The second saturation fact for \(B\) contradicts a lone \(C\) with \(a_C=3\). If \(a_C=2\), that same fact requires \(a_B\ge5\). A pair \(P,Q\) must occur. Otherwise each common middle meets at most one of \(P,Q\), and the two common middles meeting \(C\) meet neither. This gives \(a_P+a_Q\le7\), contrary to \(a_P,a_Q\ge4\). Applying the second saturation fact to both twins gives \(a_P,a_Q\ge5\). Now there must be at least 17 incidences, exceeding the upper bound \(18-a_C=16\).

## Connectivity bounds

Suppose \(F\) is \(\ell\)-connected. For a solo \(x\) of private \(J\), let \(K=N_F[x]\) and \(D=N_F(K)\setminus K\). The size of \(K\) is at least \(k-1\), and at most \(|H_J|\le2k-8\). At most \(k-2\) remotes are visible from the anchor of \(J\). Hence some vertex of \(K\) adjacent to \(x\) belongs to a different anchor's private support. The corresponding foreign private, the anchor of \(J\), and the \(a_J\) common neighbors of \(J\) are distinct distance-two witnesses for \(x\). Every vertex of \(D\) is also at distance two from \(x\). Thus \(|D|\le k-a_J-2\). Since \(|F|\ge2k-4\), \(|F\setminus K|\ge4\). Either \(D=F\setminus K\) or deleting \(D\) separates \(K\) from a nonempty remainder. Consequently \(|D|\ge\min(\ell,4)\), giving \(a_J\le k-5\) for 3-connected \(F\). If \(P,Q\) are adjacent, the other twin is an extra distance-two witness for a solo of either twin. It differs from the previously counted foreign private, which has a different anchor. Hence \(a_P,a_Q\le k-6\) for 3-connected \(F\) in that case.
