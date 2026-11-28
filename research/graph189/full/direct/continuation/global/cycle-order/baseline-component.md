# Baseline order from a component of a longest deletion path

Let G have order n, connectivity at least s≥2, and second-smallest degree k≥2s. Let its number of vertices at positive even distance from each vertex be at most k. Choose a minimum-degree vertex w, write H=G−w, and let P be a longest path of H. Let D be any nontrivial connected component of H−V(P), of order m. Then either

    n ≥ (s+1)(k−s+2)−1

or

    m ≥ 2⌈k/2⌉−2 and D is not Hamilton-connected.

This concerns every nontrivial component, with no condition on the number of components or on the degree of w.

## Proof

Every vertex of H has H-degree at least k−1. The two-contact calculation of Graph189ConeNontrivial applied to an edge within D gives 2deg_D(x)≥k−2 for each x in D. Thus 2m≥k. If m≤2⌈k/2⌉−3, every two distinct nonadjacent vertices in D have degree sum at least m+1. Prescribed-endpoint degree closure makes D Hamilton-connected.

Assume D is Hamilton-connected. A matching of j≥1 distinct edges from P into D certifies n−1≥(j+2)m+j. Indeed, splicing Hamilton paths in D into P forces each of the j−1 internal gaps between matched path positions to contain at least m vertices strictly between its ends. Each of the two tails outside the outermost marks also contains at least m vertices. Adding the j marks and the m vertices of D gives the stated count. Each splice is compared to the original longest path individually.

If m≥k−s+1, H retains (s−1)-connectivity, and both P and D contain at least s−1 vertices. For P, compare its length with a Hamilton path in D. The component-boundary matching theorem gives j≥s−1, hence n≥(s+1)m+s≥(s+1)(k−s+2)−1.

Suppose m<k−s+1. Every vertex of D has at least k−m neighbors on P since at most m−1 of its H-neighbors are internal. Choose j=k−m vertices of D; here 1≤j≤m as 2m≥k. Their sets of path neighbors meet Hall's condition since a single nonempty row already contains j neighbors. The resulting match proves

    n ≥ (m+1)(k−m+2)−1.

The excess over the required bound is (m−s)(k+1−s−m)≥0. The original graph's degree enters solely before deleting w, and all actual path splices occur in H.

## The first remaining order in both parities

Write t=⌈k/2⌉−1, so k is either 2t+1 or 2t+2. For t≥3, s≥3 and 2s≤k the first residual order m=2t is also excluded. This refinement has an independent mathematical check. The full degree-closure and split-graph argument in this section is stated on paper.

For an exterior x write Aₓ for its neighbors on P and qₓ for its degree in D. Suppose qₓ=t. The minimum internal degree is t, and any two nonadjacent vertices of the 2t-vertex D have a common neighbor. All t−1 internal nonneighbors of x thus spend its positive-even budget. For each neighbor y in D, the independent path witnesses yield

    |Aₓ| + |Aᵧ| + t−1 ≤ k.

Since |Aₓ|≥k−1−t, this gives |Aᵧ|≤2 and qᵧ≥k−3≥2t−2>t. Hence the set T of vertices of internal degree t is independent. Its size is at most t because every member has t neighbors outside T. Every missing edge incident with a vertex outside T has degree sum at least (t+1)+t=m+1 and can be filled while preserving prescribed endpoints. If |T|<t, every member of T now has degree at least t+1, so the entire component closes to a clique.

If |T|=t, every member of T is originally adjacent to all t vertices outside T. There is an edge within D−T, as every member of D−T has degree above t. For any two distinct specified members of T, alternate vertices in T and D−T, placing the two ends of this genuine edge consecutively. This gives a spanning route between the specified terminals. Each T vertex has at least k−1−t≥t contacts on P. Match all of T using Hall. The selected-terminal form of the matching inequality gives n≥(t+2)m+t+1. Here t≥s−1 and m≥k−s+1, giving the desired baseline.

The underlying local inequality applies at every order. For an edge xy in D, let Wₓᵧ consist of the exterior vertices other than y which are adjacent to x or have distance two from x, and which miss y. Then

    |Wₓᵧ| + d_H(x) + d_H(y) ≤ k + 2qₓ.

Indeed, let R consist of all exterior distance-two vertices from x. Then |Aₓ|+|Aᵧ|+|R|≤k by disjointness of the path and exterior witnesses. Every exterior neighbor of y is either x, another exterior neighbor of x, or an element of R, a population of size at most qₓ+|R|. All members of Wₓᵧ are unused in that population. Combining the bounds gives the estimate.

## The next order

For t≥3, s≥3 and 3s<k one also rules out m=2t+1. The same diameter argument holds because the neighborhoods of two nonadjacent vertices contain at least 2t members with multiplicity among just 2t−1 candidates. A vertex x of internal degree t now sees all t of its D-nonneighbors at distance two. The path witness count gives each neighbor y of x at most one contact on P, hence qᵧ≥k−2≥2t−1. The set T of tight vertices is again independent. Write U=D−T and fill all missing edges in U, using the prescribed-endpoint threshold m+1=2t+2.

If |U|≥t+3, every vertex in U now has degree at least t+2. Fill any remaining T–U and T–T edges to obtain Hamilton-connectivity. Otherwise |T|≥t−1≥s−1. Write Y for the subset of U originally touching T. One has |Y|≥t. Every member of Y has original degree at least 2t−1≥t+2, so one may fill the missing edges between T and Y. If |Y|≥t+1, all vertices now have degree at least t+1 and the component closes to a clique.

In the remaining case |Y|=t, all vertices of T were originally complete to Y. If |T|=t+1, then U=Y and alternating gives a spanning route between any two specified T vertices. The case |T|=t is impossible since the sole vertex in U−Y would only see the t others in U, yet it is nontight. If |T|=t−1, alternate members of T using distinct members of Y as separators. Put all the remaining U vertices into one gap flanked by two distinct Y vertices. This uses |T| vertices of Y in total. The route holds after the valid completion of U and hence also in D with the specified endpoints. In all cases where the whole graph fails to be Hamilton-connected, use s−1 matched T terminals; every tight vertex has at least k−1−t≥s−1 path contacts. The matching bound gives the baseline since m≥k−s+1.

Consequently, in the stated range any nontrivial D in a sub-baseline example must have at least 2⌈k/2⌉ vertices and must fail Hamilton-connectivity. Both boundary refinements were checked independently on paper.

## Relation to the published theorem

Nikoghosyan’s Corollary A applies to a λ-connected graph K when (λ+1)(δ(K)−λ+2)≥|V(K)|+2. Its conclusion bounds the circumference of the exterior of every longest cycle by min(λ−1,δ(K)−λ). Taking K to be the universal completion at w and λ=s gives the baseline for all D. The argument above discharges the Hamilton-connected component case separately and proves failure of the desired order forces the displayed size and structure for every nontrivial component.

Zh. G. Nikoghosyan, “On Some Versions of Conjectures of Bondy and Jung,” pp. 20–21. https://noad.sci.am/Content/136032/03%20%281%29.pdf.

Nikoghosyan’s separate circumference estimate gives |C|≥(q+1)(δ−q+1) with q the **maximum** exterior cycle length. Substitution of an arbitrary exhibited s-cycle is insufficient because the quadratic decreases above its midpoint. Ma, Ning and Zhao give a path-exclusion theorem with the same degree threshold and a lower bound on the total order. The independent large-order reduction in the fork still requires a formal proof of that theorem. These are different general replacements for the remaining large exterior case. [Circumference estimate](https://arxiv.org/abs/0905.1394) · [Large-order path theorem](https://arxiv.org/abs/2606.03696)

## A Hamiltonian exterior component at large order

If D has a spanning cycle, the connectivity matching still has j≥s−1 edges. Rotating that cycle to either endpoint of a required interval yields two arcs between the matched exterior vertices. The longer arc has at least ⌈m/2⌉+1 vertices. At either outermost mark one can traverse the entire m-vertex cycle after deleting a single edge. Thus the cone order is at least

    3m+2+(s−2)(⌈m/2⌉+2).

The general path theorem in Graph189LongCycleContacts is stated in H and gains the last vertex upon returning to G. It addresses Hamiltonian components for which a pair of prescribed terminals might not admit a spanning path.

## Reproduction

Run `bash replay.sh` from this folder in the pinned checkout. The geometry and minimum-degree inheritance use the previously built Graph189ActualExteriorComponent, Graph189PrescribedBatch and Graph189ConeNontrivial modules. Pinned Lean build logs are recorded beside the sources.
