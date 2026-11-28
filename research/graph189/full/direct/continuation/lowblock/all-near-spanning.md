# Every almost-spanning qualifying graph is traceable

Let G be a 2-connected graph satisfying Graph 189 with second-smallest degree k and minimum degree δ≥3. If G has a path on at least n−1 vertices then it has a spanning path. Together with the known low-degree and cut-vertex cases, the implication holds throughout the conjecture. Equivalently, in any counterexample every longest path omits a nonsingleton component, hence at least ceil(k/2)+2 vertices by the established exterior-size theorem.

Suppose P spans all vertices except z and G has no spanning path. A high singleton cannot be omitted by a longest path, so z is the unique low vertex. Its δ path contacts are internal and do not occur either consecutively (insert z) or two positions apart (exchange z for the midpoint, obtaining a new longest path omitting a high singleton). Thus their shifts give 2δ≤k. Put t=floor(k/2).

Let m be the smallest number of vertices omitted by a path containing z. The all-order near-spanning bridge gives t+1≤m≤k−δ+1; for every such longest path Q through z, the omitted H is a single Hamilton-connected graph of minimum internal degree ≥t. For clarity, the rooted exterior-degree argument uses only the distance-two cap (first section of `longest-path/gap-packing.md`); its component size implication is at least t+1 each. Each of the δ+1 inner gaps and outer tails of P determined by the contacts of z contains ≥m vertices, as replacing one by z gives a path through z. Combining n≥1+δ+(δ+1)m with the verified order bound n≤1+δ+k+δ(k+1−δ) yields m≤k−δ+1. Since this is ≤k−2, there can be only one omitted component. Its minimum degree t gives 2t≥m+1, hence Hamilton-connectedness by the Ore criterion.

Set u=k+1−m. Then δ≤u≤m and δ<m. The order bound becomes

    n ≤ m+u+δ+δ(k+1−δ) ≤ m+u+δ+mu,

because mu−δ(k+1−δ)=(m−δ)(u−δ)≥0.

On any longest path Q through z, mark its positions A touched by H. Every omitted vertex is high and, having at most m−1 internal neighbors, needs at least u marks. Group successive marks that have exactly the same singleton neighbor in H, and make each multiply attached mark a separate group. Let g be the number of groups. Between successive groups one can choose a distinct H neighbor of each boundary mark. The two chosen vertices are joined by a spanning path of H. At either outer tail, one can start a spanning path in H at any chosen neighbor. Each of these g+1 intergroup gaps and tails disjoint from z must contain at least m unmarked vertices, by maximality of Q among paths through z. At most one contains z. Therefore n≥m+|A|+gm. Since |A|≥u and δ<m, the upper bound gives g≤u.

If some H vertex owns no singleton group, its ≥u contacts require at least u multiply attached groups. Then g=u, all groups are single multiply attached marks and every H vertex is adjacent to all of A. Otherwise all m vertices own a singleton group; m≤g≤u≤m forces g=u=m, one private group per vertex, no multiply attached positions. Each such group has at least m marks. The lower bound is then n≥m+2m², contradicting the upper n≤m²+2m+δ because m≥δ+1≥4. We have proved for every longest Q through z that there are exactly u distinct marks A, each complete to H. Each H vertex must have all m−1 possible internal neighbors, so H is a clique. Its sole external neighbors are the u members of A.

Now consider the ordinary u+1 gaps and tails of Q at the distinct marks A. Their endpoints are unmarked vertices of Q in the tails, since attaching an omitted vertex at a path endpoint always extends the rooted path. Exactly one interval contains z and is shorter than m: otherwise n≥m+u+(u+1)m>m+u+mu+δ. It has at least one vertex, and the other u intervals have at least m apiece. At least one of these others, J, has exactly m: if all had at least m+1 then the n−(m+u+mu) excess would be ≥u+1>δ. Replace J by a spanning path of H through its bounding mark(s). This preserves z and the order of Q, yielding another longest rooted path whose omitted set is J.

Apply the same classification to the new path. A bounding old mark b retained on the path originally touched an endpoint of the interval J, so b must be adjacent to all J. Every member x of H is adjacent to b and none is adjacent to any J member: the vertices of J were unmarked in the first path. Thus x has m vertices of J at distance two. In addition the predecessors and successors of the u original marks around Q are unmarked (no two marks can be consecutive, since insertion of H would preserve z). They all have distance two from x. Two such shifts can coincide only across an interval of exactly one unmarked vertex. All intervals except the one containing z have length at least m, so there are at least 2u−1 distinct shifts. The interval J itself contains at most two shifts, immediately next to its bounding mark(s). It follows that x has at least

    m+(2u−1)−2 = k+u−2 > k

vertices at distance two, since u≥δ≥3. This contradiction completes the proof.
