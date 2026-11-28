# Parity cancellation at an induced two-edge path

Let G be finite and connected. Write k for its second-smallest degree and assume that every closed even-distance set E(x), including x, has size at most k+1. For a wedge u–w–v with u and v nonadjacent, put
$$
 Q=N(w)\setminus(N(u)\cup N(v)),\qquad C=N(u)\cap N(v),\qquad C_1=C\cap N(w).
$$
Let M consist of the distance-two vertices from w adjacent to neither u nor v. The three-neighborhood union U=N(u)∪N(w)∪N(v) is exactly B₂(w) minus M. In particular, |U|−d(u)−d(v)=|Q|−|C|.

**Parity covering lemma.** If M is empty then n≤3(k+1)−|Q|+|C₁|, without a diameter restriction. More generally, let T consist of the vertices equidistant at a common odd distance at least three from u,w,v. Then
$$
 |T|\ge n-3(k+1)+|Q|-|C_1|.
$$
Every geodesic from w to any member of T crosses M at its second step. In particular, if n>3k+2 then M empty implies |Q|≤|C|−1, since w is in C but outside C₁.

**Proof.** If a vertex is odd to u,w,v, the three distances are equal because successive ones differ by at most one. The common-distance-one vertices are exactly C₁. Each vertex of Q other than u and v is at distance two from both u and v through w. The endpoints u and v also belong to both E(u), E(v) by distances zero and two. Thus E(u)∪E(w)∪E(v) has at most 3(k+1)−|Q| vertices. This proves the inequality after adding C₁ and T. If w,b₁,b₂,…,t is a geodesic of odd length r≥3 to a member of T, adjacency of b₂ to u or v would put that endpoint at distance at most 1+(r−2)=r−1 from t. Hence b₂∈M. When M is empty, n≥3k+3 now implies |Q|≤|C₁|≤|C|−1. ∎

**An order-independent traceability class.** Suppose n>3k+2, G is 2-connected and
$$
 d(w)+k\le d(u)+d(v)+1
$$
for each induced wedge u–w–v. Then G is an L₁-graph in the sense of Asratian, Broersma, van den Heuvel and Veldman: d(u)+d(v)≥|U|−1 for every such wedge. Indeed, |B₂(w)|≤1+d(w)+k≤d(u)+d(v)+2. A violation of L₁ gives |U|≥d(u)+d(v)+2, forcing U=B₂(w) and M empty. The parity covering lemma now gives |U|−d(u)−d(v)=|Q|−|C|≤−1, a contradiction.

The wedge-degree hypothesis holds in particular when all degrees belong to {k,k+1}. It also permits a sole smaller vertex and unrestricted individual degrees when their local sums satisfy the stated inequality.

In this class, G is 1-tough: by Theorem 5 of A. S. Asratian, H. J. Broersma, J. van den Heuvel and H. J. Veldman, “On Graphs Satisfying a Local Ore-Type Condition”, J. Graph Theory 21 (1996), 1–10, a 2-connected L₁-graph is 1-tough except in the family containing a spanning K_{p,p+1} and contained in the join of a clique of order p with an independent set of order p+1. In that family k=p (the independent side all have degree p and all vertices have degree ≥p), n=2p+1, excluded here. Their Theorem 7(a) gives a Hamilton cycle if, in addition, every distance-two pair has two distinct common neighbors. Together with the previous bounded-order research theorem, this proves traceability for the latter class at all orders. The local-degree bound and common-neighbor condition do not follow from the unrestricted conjecture's hypotheses. The 1-toughness conclusion alone does not settle traceability. Primary source https://ris.utwente.nl/ws/files/6633608/Asratian96on.pdf
