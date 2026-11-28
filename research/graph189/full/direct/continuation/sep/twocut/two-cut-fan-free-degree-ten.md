# Connectivity two at degree ten without a circumference theorem

The independently audited [Fan-free separating-pair proof](two-cut-fan-free.md) works at \(k=10\) after the following additional treatment of a shallow side with common contacts and both private contact types. The other cases in that proof still use their same constructions at \(k=10\). This is a paper extension.

Let \(p,q\) be the anchors, \(A\) a shallow side with common ports and both private types, and \(B\) the other side. Here shallow means every high vertex of \(A\) touches an anchor. Let \(a=|A|\), \(b=|B|\), \(c,t\) count the common ports in \(A,B\), and \(\ell_A,\ell_B\) count their low vertices. Let \(L=\ell_A+\ell_B\le1\), and let \(\ell\le\ell_B\) count low nonports in \(B\). Write \(w,v\) for high \(B\) nonports which are at distance two from both anchors and from exactly one, respectively.

The minimum degree is at least three by the degree-two theorem, \(n\ge4k-5=35\) by the index-three theorem, and every edge lies in a triangle by the triangle-free edge bound \(n\le3k+2\). Each anchor contacts both sides. The large case chooses \(A\) as a minimum side across every genuine two-cut, as in the main proof. The balanced case below allows either orientation.

In the large case \(b\ge20\), the strict far-private bound makes each high private vertex of \(A\) two steps from its missing anchor. For the balanced mixed case, \(B\) is common-free and each anchor contacts at most nine vertices of \(A\) by the saturated private-port argument. A high \(A\) private vertex has at least nine internal neighbors, and its own private class has at most nine vertices, with at most one additional low nonport. It cannot remain too far from the other anchor. A low-only private representative has a high internal neighbor that touches its missing anchor. Thus both representatives are near in either application. Since one is high we have \(a\ge10\), so the high vertices of \(B\) are near at least one anchor.

The adjacent-anchor case in the main note uses \(n\le3k+1\) in the large case and \(n\le3k+2\) in the balanced mixed case. Both are impossible. For nonadjacent anchors, their mutual distance is two. The representative rows, anchor rows and common-port census give

\[
 b\le18+w+\ell-t,\qquad
 n+w\le30+c+L .
\]

The second inequality uses at most ten \(B\) ports, charged by any common \(A\) vertex.

## The opposite side has a common port

A common \(B\) port also charges every \(A\) port, so \(a\le10+\ell_A\). Using \(n=a+b+2\ge35\) and the first inequality gives \(w\ge5+t-(\ell_A+\ell)\ge4+t\). Both private types give \(c\le a-2\); the second inequality gives \(b+w\le26+L\). Since \(b\ge23-\ell_A\), we have \(w\le3+L+\ell_A\le5\). For \(t\ge1\), all these bounds force \(t=1,\ w=5,\ \ell_A=L=1,\ a=11\). The low \(A\) vertex must be a nonport, since there are eleven vertices and at most ten ports. After omitting that vertex and the two private contacts from the common count, \(c\le a-3\). This gives \(w\le4\), a contradiction.

## The opposite side is common-free

Each \(A\) anchor contact class has at most nine vertices. A private \(B\) contact would see ten opposite neighbors of its anchor at distance two if that class had size ten. It would become internally universal in \(B\) by connectedness and would then see its missing anchor at distance two through another \(B\) contact, violating its quota. Thus \(a\le18-c+\ell_A\). The two census inequalities give

\[
 n\le38-c+w+\ell+\ell_A,\qquad
 2n\le68+L+\ell+\ell_A\le70 .
\]

Equality follows throughout. In particular \(n=35\), \(L=1\), \(\ell=\ell_B\), \(a=18-c+\ell_A\), and \(b=18+w+\ell_B\). Both \(A\) contact counts are nine, with the possible low vertex a nonport. Equality in the anchor census implies that \(B\) has exactly ten ports. The ports are all high and

\[
 v=b-10-\ell_B-w=8 .
\]

The high core of \(A\) is complete. Each common \(A\) vertex counts the ten \(B\) ports at distance two. It must be adjacent to every other \(A\) port, since any nonadjacent \(A\) port would be a new exact-distance-two witness through its shared anchor. For each private type the charge in the representative-row inequality is the same for every high representative of that type. The equality of the sum of the rows saturates each individual representative's even quota. Any two nonadjacent high private vertices of \(A\) would see one another at distance two via a common \(A\) port, outside those charges. This proves completeness.

If \(A\) contained the low vertex \(z\), it would be a nonport with a high internal neighbor by connectedness. Every other high \(A\) vertex either touches \(z\) or sees it at distance two via that neighbor, which is impossible since all their quotas are already spent. Thus \(z\) would be adjacent to all \(18-c\) high \(A\) vertices. Both private types are high, so \(c\le8\). This would give degree at least ten for \(z\), a contradiction. Therefore \(A\) is a clique of high vertices, the low vertex is in \(B\), and it is a nonport.

If \(b\le20\), at most \(b-10\le10\) vertices of \(B\) are forbidden starts, counting its low vertex and all nonports. Every high nonport has internal degree at least ten and the low nonport has internal degree at least three. The ordinary rotations and degree-sum bound from the main note give a path in \(B\) beginning at a high port with at least \(\min(b,19)\) vertices. Match \(A\) through that anchor using the clique. At most two vertices in all are omitted. In particular this covers the balanced mixed equality even if \(A\) was not the originally selected minimum side.

Now \(b\ge21\), so this is the large case and \(A\) is the selected minimum side. Both \(B\) private classes have at least two vertices. Each anchor–\(B\) edge lies in a triangle and the third vertex must be another \(B\) port of the same label. There is no edge between the \(B\) private classes. If such an edge joined \(x\) and \(y\), each endpoint would count nine \(A\) ports of its own label and the missing anchor at distance two. Hence neither could have an internal second-layer vertex. Connectedness would make each universal in \(B\), forcing every high \(B\) nonport to be near both anchors and contradicting \(v=8\).

Fix a \(B\) port \(x\) of label \(p\). It sees the nine \(A\) ports of label \(p\) at distance two, so at most one vertex at internal distance two is allowed. There is one, since \(B\) is connected and \(x\) misses all \(q\)-ports. Call it \(g\) and put \(U=N_B[x]\), \(W=B\setminus(U\cup\{g\})\). These sets are anticomplete. No \(q\)-port belongs to \(U\), and at least one \(q\)-port belongs to \(W\) since there are two such ports. A \(p\)-port outside \(U\) is at distance two from \(x\) via \(p\), so any such port is \(g\). Consequently removing \(p,g\) separates \(U\) from the rest and removing \(q,g\) separates \(W\) from the rest. Both are genuine two-cuts, hence \(|U|,|W|\ge a\) by selection.

In this equality \(b=33-a\), \(a=18-c\), \(c\le8\). The recuts give \(b\ge2a+1\), so \(a\le10\), and the private types give \(a\ge10\). Thus \(a=10,\ b=23\), and \(10\le |U|,|W|\le12\).

A high vertex of \(U\) or \(W\) has at least eight neighbors within its own side, since it loses at most one anchor contact and \(g\), with no cross edges. Removing the possible low vertex reduces this by at most one. Each high induced side is Hamilton-connected by Ore, since twice seven is at least its order plus one. The gate touches both \(U\) and \(W\) by connectedness. It is not adjacent to \(x\), by choice at distance two. Thus if the gate has a high neighbor in \(U\), a spanning high-side path can start at \(x\) and end at that neighbor. If its only \(U\) neighbor is the low vertex, that nonport has degree at least three and hence at least two high neighbors within \(U\). Choose one different from \(x\), span the high side from \(x\) to it and then use the low vertex to reach the gate. For \(W\), likewise choose a high gate neighbor as a start or, if the gate touches only the low vertex there, enter through the low vertex and a high neighbor. If the gate itself is low, both sides are entirely high and the same route includes it. This yields a path from \(x\) covering all of \(B\) except possibly the low vertex. Join it through \(p\) to a spanning \(A\) path.

The new routes leave at most two total omissions, within the six-vertex allowance in the existing path gap at \(k=10\). For the other cases, the arithmetic in the main note remains valid at \(k=10\). In particular \(2k-6>k+1\), \(2(k-4)\ge k\), and \(3k-7>2k+1\). Thus the Fan-free separating-pair proof now covers every \(k\ge10\) on paper. The exact degree-ten extension has no Lean or official checker verdict.
