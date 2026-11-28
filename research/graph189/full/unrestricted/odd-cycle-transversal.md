# Graph 189 and connected induced bipartite subgraphs

Let G be a finite connected simple graph, let k be its second-smallest degree, and assume that every vertex has at most k vertices at distance exactly two. Write H=G−X, t=|X|, and assume H is connected and bipartite with an edge. Then

* If k>3t+2, each class of H has at most k+1 vertices.
* The same conclusion holds for t=1 and k≥4.

These are order bounds proved using only the second neighborhoods. In the second case, G has order at most 2k+3. Under the stronger even-distance hypothesis of Graph 189, Easwar and Johari's Theorem B therefore proves traceability. If removal of the exceptional vertex disconnects G, their cut-vertex case already applies. This proves the vertex-deletion-to-bipartite case for k≥4.

## General proof

Write A,B for the two classes of H. If the unique possible vertex of degree below k lies in H, choose A to contain it. All vertices of B have degree at least k in G. For b in B put E_b=N_H(b), a subset of A of size at least k−t. Distinct members of E_b are at distance two in G because A is independent. Whenever E_b and E_c share a vertex a, every point of their union except a is at distance two from a, so |E_b∪E_c|≤k+1. In particular if E meets F, at most t+1 points of F are missing from E.

If E and D both meet F, then at most 2(t+1) points of F are missing from their intersection. Since |F|≥k−t>2(t+1), E and D meet. Connectedness of H makes its edge-intersection graph on the sets E_b connected. Transitivity now makes all pairs of these sets intersect. Their indices B are independent and pairwise at distance two in G. Thus |B|≤k+1.

Every vertex of A of degree at least k in G has at least k−t neighbors in B. As 2(k−t)>k+1, any two such vertices share a neighbor and are at distance two. There are at most k+1 high vertices in A. If there are exactly k+1 and an additional low vertex z, choose b in N_H(z), which exists by connectivity. Its at least k−t≥2 neighbors in A include a high vertex a. Now a has its k high companions and z all at distance two in G, a contradiction. Therefore |A|≤k+1 as well. In particular |G|≤2k+t+2.

## A single removed vertex

Write X={x}. Each E_i, indexed by b_i∈B, has size at least k−e_i, where e_i=1 if b_i is adjacent to x and e_i=0 otherwise. We prove that two sets meeting a third must meet each other as soon as k≥4. Suppose that E_0 and E_2 are disjoint but both meet E_1. For i=0,2 write U_i=|E_i∪E_1|. Since every point of E_1 is outside at least one of E_0,E_2,

    |E_1| ≤ U_0−|E_0| + U_2−|E_2|.

Always U_i≤k+1. Furthermore, if e_(2−i)=1 and at least one of e_i,e_1 equals 1, then U_i≤k. Indeed, choose a∈E_i∩E_1. If a is not adjacent to x, then it sees x at distance two. If it is adjacent to x, it sees b_(2−i) at distance two, because it does not belong to the disjoint E_(2−i). Either way a has an additional distance-two vertex outside A.

If e_0=e_2=0, both sets have size at least k, so |E_1|≤2. If e_0=e_2=1, both U_i≤k, and |E_i|≥k−1 again gives |E_1|≤2. Both contradict |E_1|≥k−1≥3. In the mixed case take e_0=1,e_2=0. The ordinary union bounds give |E_1|≤3. This already contradicts k≥5. For k=4 it forces |E_1|=3 and e_1=1. The strengthened bound U_2≤k then improves the right side to at most two, again impossible.

This proves transitivity of intersection. The remainder of the general proof applies unchanged since 2(k−1)>k+1 for k≥4.

## A single deleted edge

For k≥3 the conjecture also holds if deleting an edge pq makes G bipartite. The triangle-free case is already settled by the fork. Otherwise pq belongs to every triangle, so choose b adjacent to p and q, and color G−pq with b∈B and p,q∈A. No geodesic starting at b can traverse pq, since reaching the latter endpoint directly from b shortens its prefix. All members of B are consequently at even distance from b in G, giving |B|≤k+1. Any high a∈A different from p,q has at least k neighbors in B. Every other high member of A has at least k−1, and 2k−1>k+1. Hence a sees every other high member of A at distance two. There are at most k+1 high members, so |A|≤k+2. If no such a exists, |A|≤3 directly. Thus |G|≤2k+3 and the Easwar–Johari order theorem applies.

External theorem: Rohun Easwar and Shaurya Johari, Conditions for traceability under a bound on the size of even-distance sets, arXiv:2609.11719, Theorem B. The conclusions above are mathematical proofs, not a Lean-checked proof of the full registered target.

## Removing the connectedness assumption

Suppose G is 2-connected, t≥1, H=G−X is bipartite and k>3t+1. Then H has at most one component with two or more vertices. Every isolated vertex of H has degree at most t in G and is therefore the unique possible low vertex.

Put r=k−t. Each high vertex of H has at least r neighbors in H. Each member u of a nonsingleton component C of H has a high neighbor v in C. For high u this follows from r≥2 and uniqueness of the low vertex. For low u it follows since u has a neighbor in C. Besides u, the neighborhood N_H(v) contains at least r−1 vertices, all at distance two from u, since its color class in H is independent even in G. Thus u can see at most k−r+1=t+1 vertices at distance two outside C.

A high x∈X has at least k−t+1 neighbors in H. If it touches two nonsingleton components C,D, the preceding count from an x-neighbor in C bounds all its H-neighbors outside C by t+1. The count from an x-neighbor in D then bounds its H-neighbors in C by t+1. This gives k−t+1≤2t+2, contrary to k>3t+1. Every high x has neighbors in some nonsingleton component, as it has more than one H-neighbor. Assign x to this unique component; it has at least r neighbors there, allowing for the possible isolated low vertex elsewhere.

Suppose two adjacent high vertices x,y∈X were assigned to different components C,D. At least r neighbors of y in D are at distance two from x. Hence x has at most t distance-two vertices in C. Choose a high neighbor u of x in C. At least r−t of its opposite-color H-neighbors must also be adjacent to x, and r−t≥2, so choose a high one v. The H-neighborhoods of u and v, lying in opposite classes, give at least 2r distinct vertices of C. All points of these two neighborhoods not adjacent to x are at distance two from x. Thus x has at least 2r−t>k neighbors in C. Each is at distance two from y, contradiction.

Delete the unique low vertex if it exists. The remaining graph is connected by 2-connectivity. Every remaining vertex belongs to a nonsingleton H-component or is an X-vertex assigned to one. Every edge now has both endpoints assigned to the same component, using the preceding paragraph for X–X edges. Therefore there was at most one nonsingleton H-component. A nonsingleton component contains a high vertex and so survives the possible deletion.

Consequently, for arbitrary odd cycle transversal X with k>3t+2, the connected proof applies to the unique nonsingleton component of H (each member has exactly the same H-neighborhood as before). This gives n≤2k+t+3, with the final extra vertex possible only when the low vertex is isolated in H. The case of no nonsingleton component has order at most t+1 directly. For t≥2 and k≥3t+3 we have n≤3k−4; the already established order theorem in /tmp/full189nov28/split-ball/strong-order.md gives traceability. For t=1 use the sharper single-vertex result. Thus a counterexample with large second-smallest degree must have an odd cycle transversal of size at least (k−2)/3, rounded upward.

## Sharper integer threshold

In the connected-component proof the conclusion |A|,|B|≤k+1 in fact holds for k≥3t+1 and t≥1. Suppose disjoint E_0,E_2 both meet E_1 as in the single-vertex argument. Write P_i=N_G(b_i)∩X and p_i=|P_i|. If (P_i∪P_1)∩P_(2−i) is nonempty, take x in that intersection. Any a∈E_i∩E_1 has an extra distance-two vertex outside A, either x when a is not adjacent to x, or b_(2−i) when a is adjacent to x. Hence |E_i∪E_1|≤k in that case. Let q_i denote the 0–1 indicator of this nonempty intersection. As |E_i|≥k−p_i, the two union bounds imply

    k ≤ 2 + p_0+p_1+p_2 − q_0−q_2.

When t≥2, if the sum of the p_i is at least 3t−1, each P_i misses at most one element of X and at most one P_i misses any. Therefore all three P_i have a common element and both indicators equal one. If their size sum is at most 3t−2, the ordinary bound is already at most 3t. This contradicts k≥3t+1. The case t=1 is the preceding single-vertex proof. The final order conclusion with arbitrary X therefore holds already at k≥3t+2, from the component argument. For t=2,k=8 the resulting n≤21≤3k is covered by the separate earlier paper proof for n≤3k. For every t≥2 and k≥3t+2, the inequality n≤2k+t+3≤3k holds. Accordingly, a counterexample must have odd cycle transversal number at least ceil((k−1)/3), with the vertex-deletion result separately ruling out t=1 already for k=4.

## The remaining one-vertex case k=3

For every k the full Graph 189 conjecture holds when deleting a single vertex yields a bipartite graph. For k≤2, and for k=3 with minimum degree≤2, apply the earlier minimum-degree-two theorem in /tmp/full189nov28/split-ball/degree-two-all-diameters.md and Easwar–Johari's cut-vertex theorem. This leaves k=3, minimum degree three. All vertices are high, so the formalized distance-five endpoint and diameter bounds in the upstream R1 reduction imply diameter at most four. As before, G−x is connected and bipartite with classes A,B.

For either class C with |C|≥5, at most three vertices of C neighbor x. Otherwise four such vertices, pairwise at distance two, saturate every one of their second neighborhoods. No H-neighbor of this four-element set could touch another member of C. This would disconnect H (or, equivalently, split the intersection graph of its same-side distance-two relation), a contradiction.

Every a∈C not adjacent to x must then have distance two from x. Otherwise, for any a'∈C a path of length three from a to a' would have to use x, because H is bipartite. Since a is not adjacent to x, the length-three path must reach x in two steps. This is excluded by assumption. As there are no edges in C and every pair has distance at most four, all other |C|−1≥4 vertices of C would thus be at positive even distance from a, a contradiction.

If both A,B have size at least five, at most six vertices of H neighbor x and every other vertex of H is at distance two from x, of which there are at most three. This contradicts |H|≥10. Hence one class, say A, has size at most four. If |B|≥5, choose b∈B not adjacent to x, possible by the first bound. It has at least three neighbors in A. Every other b'∈B has at least two neighbors in A, so it shares one with b. Thus b sees at least four vertices at distance two, again impossible. Both classes have at most four vertices, n≤9, and the Easwar–Johari order theorem applies. This final k=3 argument uses the full even-distance hypothesis through the global diameter reduction. No finite enumeration is involved.

## Triangle transversals and disjoint triangles

The preceding results imply the following stronger obstruction. If a vertex set X of size t meets every triangle of G and k≥3t+3, then G is traceable under the hypotheses of Conjecture 189. Equivalently, any counterexample requires a triangle transversal of size at least ceil((k−2)/3). In particular every counterexample contains at least ceil((k−2)/9) pairwise vertex-disjoint triangles. Independently, the settled triangle-free branch always forces at least one triangle.

It suffices to prove that H=G−X is bipartite. We know it is triangle-free, and we impose no connectivity condition on H here. For each high vertex b of H let E_b=N_H(b); its cardinality is at least k−t. For high b,c and a∈E_b∩E_c, every element u of E_b∪E_c other than a is at distance exactly two from a in G. To see this, a and u have either b or c as a common H-neighbor, and if adjacent in G their edge would also belong to the induced graph H and create a triangle. Thus |E_b∪E_c|≤k+1. For any three high-index sets E,F,D with E∩F and F∩D nonempty, the portion of F outside each outer set has size at most t+1. Since |F|≥k−t≥2t+3, the sets E and D intersect. This proves that intersection is transitive on these high-index neighborhoods. We only use the ordinary union bound here; no extra-witness improvement from the bipartite case is assumed.

Suppose H had an odd cycle with distinct vertices v_0,...,v_(m−1), indices modulo its odd length m≥5. The cyclic ordering with increment two visits all m vertices, and consecutive indices in that ordering have intersecting neighborhoods because of the intervening original cycle vertex. If the unique possible low vertex is on the cycle, remove its position from the increment-two ordering and start immediately after it. The resulting linear order of all high cycle vertices has consecutive intersecting neighborhoods (the intervening original neighbor need not be high). If there is no low cycle vertex, simply cut the increment-two ordering anywhere. By transitivity all high cycle vertices have pairwise intersecting H-neighborhoods. Two consecutive original cycle vertices can be chosen high since m≥5 and at most one is low. Their shared H-neighbor makes a triangle in H, contradiction. Hence H has no odd cycle and is bipartite.

When t=0 apply the established triangle-free theorem. When t=1 apply the one-vertex theorem above. For t≥2, k≥3t+3 implies k>3t+1, so the component argument and the connected bipartite order proof give n≤2k+t+3≤3k−4 for a 2-connected graph. The prior 3k−4 order theorem gives traceability; non-2-connected graphs follow from Easwar–Johari. Finally, the vertices in any maximal collection of pairwise vertex-disjoint triangles form a triangle transversal. If its cardinality is 3m, the inequality k≥9m+3 forces traceability. Thus in a counterexample 9m+2≥k, proving the stated packing bound. The odd cycle transversal bound above is stronger by one in its numerator but concerns a different parameter.
