# Packing attachment positions on a longest path through the low vertex

Retain the hypotheses, attachment notation, and near-spanning result of [the attachment argument](attachments.md). In particular, assume that \(G\) is 2-connected with \(n\leq3k+2\), and that in a hypothetical nontraceable graph a longest path \(P\) omits just the unique low vertex \(z\). This is guaranteed by the cone argument whenever \(k\geq3\). We show that \(\delta=d(z)\geq5\) is impossible.

## Internal degree in the omitted components

Let \(Q\) be a longest path through a prescribed vertex, and suppose every omitted vertex is high. Each omitted vertex \(x\) has an omitted neighbor \(y\). All neighbors of \(x\) and \(y\) outside \(Q\) lie in their common omitted component \(C\). The set
\[
 N_C(y)\setminus\bigl(N_C(x)\cup\{x\}\bigr)
\]
consists of distance-two witnesses from \(x\) outside \(Q\), and has size at least \(q_y-q_x\) since \(y\in N_C(x)\setminus N_C(y)\) and \(x\in N_C(y)\). It is disjoint from all witnesses counted on \(Q\).

If \(a_x\leq k/2\), high degree implies \(q_x\geq\lceil k/2\rceil\). Otherwise the shift count \(a_x+r_x\leq k\) forces a nonsingleton run, and the rooted overlap inequality strengthens to
\[
 k \geq a_x+a_y-1+q_y-q_x\geq a_x+k-1-q_x.
\]
Thus \(q_x\geq a_x-1\geq\lfloor k/2\rfloor\). This improves the rooted omitted-component size bound by giving minimum internal degree at least \(\lfloor k/2\rfloor\). The same proof in an unrooted longest path gives \(q_x\geq a_x+1\) in the nonsingleton-run branch, and hence \(q_x\geq\lceil k/2\rceil\) for every omitted high vertex with an omitted high neighbor.

## A gap and its omitted component

The \(\delta\) attachment indices of \(z\) on \(P\) span at most \(n-4\). If \(g\) is the smallest gap, inserting \(z\) in place of the \(g-1\) intervening vertices gives a path through \(z\). Choose a longest path \(Q\) through \(z\). If \(m\) vertices are omitted by \(Q\), then
\[
 \lfloor k/2\rfloor+1\leq m\leq g-1\leq \left\lfloor\frac{3k-2}{\delta-1}\right\rfloor-1. \tag{3}
\]
For \(\delta\geq4\) the upper bound is at most \(k-2\). The rooted component size bound implies that the omitted vertices form a single component \(C\), since \(m<2(\lfloor k/2\rfloor+1)\). By the internal degree result, the minimum degree in \(C\) is at least \(\lfloor k/2\rfloor\geq(m+1)/2\), so \(C\) is Hamilton-connected. One way to see this is to add a degree-two marker adjacent to two specified endpoints. Every nonadjacent pair of original vertices has degree sum at least \(m+1\), the augmented order. Ordinary cycle closure completes the original vertices to a clique and preserves Hamiltonicity. Thus there is an original Hamilton cycle through the marker, and deleting it gives a spanning path of \(C\) with the specified endpoints.

## Counting attachment incidences

Divide the internal positions of \(Q\) into the two sides of \(z\), assigning the position of \(z\) itself to either side if it is internal. Call an internal position an attachment if it has a neighbor in \(C\). Any two distinct attachment positions on the same side can use two distinct prescribed neighbors in \(C\) if at least one position has more than one neighbor in \(C\). A spanning path between those neighbors can replace the intervening vertices of \(Q\); this preserves \(z\) because it lies outside the replaced interval or at an endpoint. Hence such attachment positions differ by at least \(m+1\).

On a side with \(L\) usable positions, let \(M\) attachment positions have at least two neighbors and \(S\) have exactly one neighbor in \(C\). A gap between consecutive attachments that involves one of the \(M\) positions has at least \(m\) empty positions. If \(S>0\), there are at least \(M\) such gaps: a run of \(j\) positions with at least two neighbors has its \(j-1\) internal gaps and at least one boundary gap. Thus \(L\geq S+M+mM\), and the incidence count from this side is at most \(S+mM\leq L\). If \(S=0\) and \(M>0\), the \(M-1\) gaps show \(L\geq M+m(M-1)\), so the incidence count is at most \(mM\leq L+m-1\). This latter upper bound is valid when \(S=M=0\) as well.

Summing over the two sides, which together have \(n-m-2\) positions, gives
\[
 m(k-m+1)\leq n+m-4,\qquad m(k-m)\leq n-4\leq3k-2. \tag{4}
\]
If there is even one attachment position with precisely one neighbor in \(C\), the stronger bound \(m(k-m+1)\leq n-3\) holds. If there are none, the total number of attachment positions is at most
\[
 2+\left\lfloor\frac{n-m-4}{m+1}\right\rfloor. \tag{5}
\]
Indeed if both sides are nonempty in attachments, the successive gaps on each side yield the formula. If only one side is nonempty, the simpler bound is \(1+\lfloor(n-m-3)/(m+1)\rfloor\), which is at most (5).

## Minimum degree at least five

The almost-spanning argument gives \(2\delta\leq k\), hence \(k\geq10\). With \(\delta\geq5\), (3) gives \(m\leq\lfloor(3k-6)/4\rfloor\). In particular
\[
 m(k-m)\geq (k+1)(k+6)/8>3k-2\quad\text{for } k\geq16,
\]
since the strict inequality is equivalent to \(k^2-17k+22>0\). This contradicts (4). For \(k=12,13,14,15\), the right endpoint for \(m\) is respectively \(7,8,9,9\), yielding \(m(k-m)\geq35,40,45,54\) respectively by monotonicity on integers \(m>k/2\). These exceed \(3k-2\) in each case.

It remains to examine \(k=10,11\). In both cases \(\delta=5\), (3) gives \(m=6\), and the internal degree bound implies that \(C\) is a clique. It requires \(m(k-m+1)=30\) or \(36\) incidences, whereas \(n-3\leq29\) or \(32\), respectively. Accordingly every attachment position has at least two neighbors in \(C\). By (5) there are at most five such positions in either case. This already contradicts \(k=11\), since each vertex of \(C\) needs at least six attachments.

For \(k=10\), every vertex of \(C\) must see all five positions. Also a shortest gap of \(P\) between consecutive attachments of \(z\) has size seven by (3) and \(n\leq32\). Therefore we may choose \(Q\) to be precisely the splice through \(z\) over this gap, which omits the six intervening vertices and is maximal among paths through \(z\). The two vertices immediately before and after \(z\) in this \(Q\) are attachment positions, since each was adjacent in \(P\) to the adjoining vertex in the six-vertex omitted block. Thus all six omitted vertices lie at distance two from \(z\). On the original \(P\), the \(2\delta=10\) shifted distance-two witnesses from \(z\) intersect that block in only its first and last vertices, since the block lies between consecutive attachments of \(z\). Altogether \(z\) has at least \(6+10-2=14\) distance-two vertices, a contradiction.

Consequently \(G\) is traceable when \(n\leq3k+2\) and \(\delta\geq5\). The cone theorem used to obtain the almost-spanning path already applies throughout this range.
