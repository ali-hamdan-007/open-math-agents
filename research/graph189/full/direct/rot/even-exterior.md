# Exterior components of minimum order on a longest path

Let G be a finite simple 2-connected graph, let k be its second-smallest degree counted with multiplicity, and assume every vertex has at most k other vertices at positive even distance. Call a vertex high if its degree is at least k. There is at most one other vertex. All paths here are simple. The proof is purely combinatorial.

**Theorem.** For every longest path P, each component of G−V(P) is either the singleton low vertex or has at least floor(k/2)+2 vertices. In particular the previously allowed exterior size k/2+1 is impossible for every even k. There is no order or diameter restriction.

We use the earlier path-attachment and size count in `graph189/full/longest-path/attachments.md`. For k≥3 it already gives the bound ceil(k/2)+1. The only additional case to exclude is a component C of h+1 vertices at k=2h. The k=2 case is handled directly at the end.

## The structure at equality

Write P as an ordered sequence of L vertices numbered from 1. In the even equality case, the earlier count shows that C is a clique, each high member has exactly h common neighbors A on P, and the positions of A are separated by at least h+2. For reference, each high vertex in C needs at least h path attachments. For any exterior vertex x, mark its attachments on P. Their predecessors and successors are at distance two from x. The marks are internal, none consecutive, and the two shifts have cardinality equal to the number of marks plus the number of maximal runs with mark spacings two. For adjacent exterior x,y, if x has a nonsingleton run, the shifted marks and the additional marks of y give at least |A_x|+|A_y|+1 witnesses at distance two from x. Indeed y has no marks at index difference one or two from any x-mark (inserting x,y, or substituting both for one path vertex); thus common marks occur only in the singleton runs. A high pair therefore has only singleton runs, since a nonsingleton violates the cap. Each member has exactly h attachments, and is adjacent to all remaining members of C. Every high member then has a high neighbor and the same argument applies. Existence of a high pair is automatic for |C|≥3 unless C consists of low center and high leaves. A high leaf has just one exterior neighbor and at least k−1 marks. Their shifts exhaust the cap, whereas another leaf gives one more distance-two vertex via the center. The clique and common mark set follow, since for a high x the shifts exhaust its distance-two budget and any attachment of an exterior neighbor y outside A_x cannot be a shift of A_x by the insertion of x,y. This argument also shows that a possible low member of C has all its attachments in A. Distinct attachment positions can be connected through every vertex of the clique, so all intervening gaps have at least m=h+1 interior vertices. Both outer tails have at least m vertices as well, since one can replace an entire tail by C through a high contact. There are distinct high contacts to route between two A vertices when h≥2.

Let B be the 2h path positions immediately preceding and following A. For a fixed high x in C these are all its positive even-distance vertices. Set W=V(G)−(A∪B∪C). The vertices of W are nonadjacent to A, since x sees A and has exactly B as its second layer. Each w∈W is at distance three from x: it is not in its first two layers, and any distance at least four would produce a forbidden fourth-layer vertex on a geodesic. Thus W is covered by the B-neighborhoods. The h−1 gaps and two tails yield

    L ≥ h+(h+1)m,       |W| ≥ (h+1)m−2h = h²+1.                  (1)

These conclusions apply to every longest path with the same vertex set. In particular the two endpoints lie in W: the h+1 vertices in either outer tail keep the endpoints outside the marked positions and their immediate shifts. An endpoint has no neighbor off the path and no neighbor in A.

## A second count from the attachment positions

Suppose h≥3. For each b∈B select its next path neighbor in the direction away from the marked position it brackets. This produces 2h distinct vertices in W since each gap has at least four interior vertices. Denote these representatives by W₀. For a∈A put d_a=|N(a)∩A| and S_a=N(a)∩B. Let U_a consist of the 2(d_a+1) brackets of a and its neighbors in A. At exact distance two from a we find three disjoint sets:

* the h−1−d_a missed members of A, via a common high vertex of C;
* U_a−S_a, via the associated neighbor of a in A (the two own brackets are in S_a);
* the |S_a| distinct representatives of S_a in W₀, via their brackets.

Consequently at most h−1−d_a−|S_a−U_a| members of W−W₀ are at distance two from a. Each member of W−W₀ is at distance two from some a by the B-cover. Set D=Σd_a, E=Σ|S_a−U_a| and write |W|=h²+1+s with s≥0. Summing yields

    D+E+s ≤ h−1.                                                  (2)

In particular s≤h−1. Let g₀,…,g_h be the numbers of unmarked vertices in the path's two tails and h−1 intervening gaps, each at least m. Its path excess s_P=Σ(g_i−m) is at most s by (1) and the definition of W. Orient P from its left endpoint e. This endpoint can have at most g₀−1 neighbors in the initial tail and has no neighbor in A. In each later interval, none of the first m positions after a mark j is a possible pivot for e. Rotating through such a pivot t gives the endpoint formerly at t−1, at fewer than m positions from j along the rotated path. This violates the tail bound on that path. Consequently

    deg(e) ≤ g₀−1+Σ_{i=1}^h(g_i−m) = m−1+s_P ≤ 2h−1.

The identical inequality at the other endpoint contradicts the definition of k. This proves the theorem for every h≥3 without a finite computation.

For h=2 there are precisely two marks a,c. If they are nonadjacent, each sees the other at distance two and hence at most three members of W there. If they are adjacent and one sees all B, that mark sees all W at distance two and |W|≤4. In the remaining adjacent case each misses a bracket in B, seen via the other mark, leaving at most three members of W at distance two from each. The B-cover gives |W|≤6 in every case. Thus s≤1, and the same endpoint bound gives degrees at most three at both endpoints.

Lastly at h=1 any exterior singleton high vertex needs at least two path attachments with at least three shift witnesses, violating k=2. In a two-vertex exterior C choose a high x. It needs at least one attachment, and its shifts bound gives precisely one, at a. All path attachments of the other member would be at distance two from x unless they are a, hence must be shifts of a; a shift contact would insert the pair between consecutive positions, impossible. Thus C has the unique attachment a, contrary to 2-connectivity.

## A degree bound using the full even-distance cap

For any high exterior x with a high exterior neighbor, let q_x=d_C(x), f_x be the number of vertices at even distance at least four from x, and t_x the number of vertices of other exterior components at distance two from x. Then

    2q_x ≥ k+f_x+t_x.

If all of x's runs are singletons, their shifts give 2a_x vertices on P where a_x=d(x)−q_x. The cap gives 2q_x≥2d(x)−k+f_x+t_x. Otherwise take a high exterior neighbor y. The nonsingleton overlap bound proved above gives at least a_x+a_y+1 witnesses on P. The vertices of N_C(y)−(N_C(x)∪{x}) contribute at least q_y−q_x further distance-two vertices inside C. Together these disjoint counts give

    2q_x ≥ d(x)+d(y)−k+1+f_x+t_x.

For k≥3 every omitted high x has a high exterior neighbor: if x has no exterior neighbor its shifts contradict the cap. If its sole exterior neighbor is the low z, its k−1 or more marks and their shifts use the whole budget, forcing exactly k−1 marks in one run and all neighbors of z outside P except x to be absent. Every attachment of z must belong to the marks of x, yet every such mark has another one two positions away (k−1≥2); the two-vertex splice forbids them all. This would give d(z)=1. The k=2 exception to the argument also produces a singly attached pair and contradicts 2-connectivity as above.

In particular whenever a path leaves at most floor(k/2)+1 vertices, every longest nonspanning path can omit only the singleton low vertex. The previous paper then forces 2δ≤k for k≥3, where δ is the minimum degree. The proof above does not assert that every graph has a path meeting this new omission threshold.
