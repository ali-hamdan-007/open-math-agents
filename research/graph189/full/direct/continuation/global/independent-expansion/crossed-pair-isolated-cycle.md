# One crossed pair and a short isolated exterior cycle

Let a 2-connected Graph 189 graph have second-smallest degree \(k\ge26\), order \(n\le3k+2\), and a minimum-cycle cone 2-factor comprising the apex cycle and three exterior cycles \(A,B,C\). Suppose an edge joins \(A\) and \(B\), while \(C\) has no edge to either of them and \(3\le |C|\le5\). Then \(G\) has a Hamiltonian path. This is a paper reduction using the existing longest-path gap theorem.

Open the apex cycle into \(P\) and write \(p=|P|\), \(m=|A|\), \(s=|B|\), \(M=m+s\), \(r=|C|\), and \(h=\lceil k/2\rceil\). The [apex path argument](three-cycle-splices.md) works with any number of exterior cycles. It gives \(p\ge2k+1\) and \(M+r\le k+1\). Both endpoints of \(P\) have no exterior contacts. To contradict the gap theorem, it suffices to build a path omitting at most \(h+1\) vertices.

## Splice the crossed pair

The no-switch degree bounds and the heavy-vertex argument in [the crossed-pair proof](three-cycle-splices.md#adjacent-exterior-cycles) use only the two cycles \(A,B\). They give a path spanning \(A\cup B\), with high endpoints \(a\in A,b\in B\) satisfying
\[
d_B(a)\le\lfloor s/2\rfloor,\qquad d_A(b)\le\lfloor m/2\rfloor.
\]
Each of these cross-degrees is at most the opposite order minus one. Denote the two endpoints' \(P\)-contact sets by \(X,Y\) and put \(c=\lfloor m/2\rfloor+\lfloor s/2\rfloor\). The absence of edges to \(C\) gives
\[
|X|,|Y|\ge k-M+2\ge r+1,\qquad
|X|+|Y|\ge2k+2-M-c.
\]

Put \(L=h+2-r\). Any mark from \(X\cup Y\) has at least \(L\) vertices of \(P\) before it and at least \(L\) after it. Otherwise the crossed-pair path can be attached to the longer retained part of \(P\), and the omitted tail together with \(C\) has order at most \(h+1\). Distinct opposite marks must have index difference at least \(L+1\), since a closer gap permits a splice with fewer than \(L\) missing path vertices.

The span of the marked positions, including its endpoints, is at least \(|X|+|Y|+L\). If the sets are disjoint there is a transition between pure \(X\) and pure \(Y\), with a gap of at least \(L\) unmarked positions. For intersection size \(e>0\), group the pure runs by type and let every common mark form its own group. Adjacent groups have at least \(L\) unmarked positions between them. With both pure types the bound is \(|X|+|Y|-e+(e+1)L\). With only one pure type we have \(e\ge r+1\), so the bound \(|X|+|Y|-e+eL\) is greater than \(|X|+|Y|+L\). If all marks are common, \(e\ge r+1\) and the bound \(e+(e-1)L\) is again larger than \(|X|+|Y|+L\). These comparisons use \(L\ge10\).

Let \(\tau\) be the sum of the two outer tails' excess lengths above \(L\). Including the tails gives
\[
n=p+M+r\ge 3L+|X|+|Y|+M+r+\tau
\ge2k+3h+8-2r-c+\tau.
\tag{1}
\]
For \(r=3\), using \(c\le\lfloor (k-2)/2\rfloor\) gives \(n>3k+2\).

For \(r=4\), \(c\le\lfloor(k-3)/2\rfloor\). Equation (1) contradicts \(n\le3k+2\) for odd \(k\). For \(k=2h\), equality forces \(\tau=0\), \(c=h-2\), and \(k-4\le M\le k-3\), hence \(p\le2k+2\).

For \(r=5\) and \(k=2h-1\), \(c\le h-3\). Equation (1) forces \(\tau=0\), \(c=h-3\), and \(M\ge k-5\), hence \(p\le2k+2\). For \(r=5\) and \(k=2h\), (1) gives \(h-4+\tau\le c\le h-2\). In particular \(\tau\le2\), \(M\ge k-8\), and \(p\le2k+5\).

Attach the crossed-pair path at the extreme mark with the shorter outer tail, discarding only that tail. The retained part of \(P\) is one interval of order \(N=p-\lambda\), where \(\lambda\) is the discarded tail length. The new path omits \(\lambda+r\) vertices and still contains one original endpoint of \(P\), which has no contact in \(C\). Each high vertex of \(C\) has at least \(k-r+1-\lambda\) contacts in this interval. Choose \(r-1\) high vertices on \(C\). Count each retained position with weight equal to the number of those chosen vertices it touches.

## Add vertices of the isolated cycle

For \(r=4\), the forced regime is \(k=2h\) and \(\lambda=L=h-2\). A same-root pair of consecutive positions allows insertion of that root at no cost. Contacts of distinct roots at index difference at most three permit a cycle-arc splice gaining at least one vertex, since the longer arc contains at least three vertices. In the absence of these splices, consecutive occupied indices have difference at least two, or at least four as soon as one index has weight at least two. With weights at most three this difference is at least two thirds of the two weights' sum. If \(W\) is the total weight, summing across the consecutive marked pairs gives
\[
3(h-1)\le W\le \tfrac34(N-1)+3\le \tfrac94 h+\tfrac{21}{4},
\]
since \(N\le3h+4\). A single occupied index also satisfies the upper bound. The inequality is impossible for \(h\ge13\).

For \(r=5\) and \(\lambda=L=h-3\), one net vertex again suffices. Consecutive contacts to the same root would gain one. Contacts to distinct roots at index difference at most four gain at least one by a longer cycle arc, which contains at least four vertices. If neither is possible, the index difference between consecutive marked positions is at least two, or at least five if either is multiple. With weights at most four this is at least five eighths of the two weights' sum. Now \(N\le3h+8\) in either parity, and
\[
4(h-2)\le W\le \tfrac45(N-1)+4\le \tfrac{12}{5}h+\tfrac{48}{5}
\]
is impossible for \(h\ge13\).

It only remains that \(r=5\), \(k=2h\), and \(\lambda=L+1=h-2\). Since we chose the shorter tail, both tails have excess at least one. Equation (1) forces \(c=h-2\), \(M=k-4\), \(n=3k+2\), and \(p=2k+1\). Here \(N=3h+3\), and at least two net vertices are required. Any distinct roots with contacts at index difference at most three give this gain by the longer arc. If there is no such pair, group the singleton runs of each root and make every multiple index its own group as above. Let \(q\) be the number of occupied positions, \(g\) the number of groups, and \(u\le g\) the number of multiple groups. There are at least three empty positions between groups. The retained original endpoint of \(P\) supplies one additional empty position, so
\[
4(h-2)\le W\le q+3u\le q+3g\le N+2=3h+5.
\]
This is impossible for \(h>13\). At \(h=13\) equality throughout forces every group to be a single position of weight four, and consecutive groups to have index difference four. There are eleven groups because \(W=44\). The four chosen high vertices include two consecutive cycle vertices. Any two consecutive groups offer contacts to these two adjacent roots, so the whole 5-cycle can be spliced across their gap of four, dropping three path vertices and gaining two. This finishes the last case.
