# A rooted local Ore criterion and the exceptional low degree

Let G be finite, simple and connected, with a prescribed vertex z. For each induced two-edge path u,w,v let

    j(u,w,v) = |N(u)∪N(w)∪N(v)|−d(u)−d(v).

If j≤0 whenever u,v are both distinct from z, then G has a Hamiltonian path starting at z. The unrestricted local Ore theorem of Hasratian and Khachatrian gives Hamiltonicity when every wedge satisfies their condition. The rooted argument below uses the successor incidence count also used in Lemma 13 of Asratian, Broersma, van den Heuvel and Veldman, [On graphs satisfying a local Ore-type condition](https://ris.utwente.nl/ws/files/6633608/Asratian96on.pdf). We make no claim of priority for this general graph criterion.

**Proof.** Take a longest path P subject to starting at z. If P does not span, choose an exterior vertex u touching P. Its neighbor set on P is a nonempty set W. The free end of P is not in W, so each w in W has a successor s(w). Write U for the set of these successors. We have z outside U, and U disjoint from N(u), since u could otherwise be inserted into P. The set U is independent: if s(w_i) and s(w_j) were adjacent for w_i preceding w_j, follow P to w_i, take w_i,u,w_j, follow P backwards until s(w_i), then go to s(w_j) and follow the remaining suffix. This preserves the start z and adds u. Every common neighbor of u and s(w) lies in W, since an outside common neighbor y allows w,u,y,s(w) in place of the edge w,s(w).

For each w set Q_w=N(w) minus (N(u)∪N(s(w))). The distinct vertices u and all of N(w)∩U belong to Q_w. Since j=|Q_w|−|N(u)∩N(s(w))| we obtain

    j(u,w,s(w)) ≥ 1+|N(w)∩U|−|N(s(w))∩W|.

Sum over W. The two neighbor counts count exactly the same edges between U and W, so the sum of the local defects is at least |W|. Both endpoints of every one of these wedges differ from z; their assumed nonpositive defects give the contradiction.

**Graph 189 consequence.** Let k be the second-smallest degree, take z of minimum degree, let Δ be the maximum degree, and assume the original even-distance cap. Then all endpoints other than z have degree at least k. By the [penultimate-vertex wedge inequality](../verify/wedge-order-and-hamiltonicity.md), any such wedge with defect ≥1 requires

    n ≤ 3k+1 + k(d(w)+e(w)−d(u)−d(v)) ≤ (3+Δ−k)k+1,

where e(w) counts all other vertices at even distance from w. At greater order there is a Hamiltonian path starting at z. If no exceptional vertex exists, any root may be chosen in this argument. This bound is independent of the minimum degree. In particular if Δ=k, any order n>3k+1 is covered and n≤3k+2 was previously settled. This proves the conjecture when all vertices except possibly one have the same degree k, with no restriction on how far the exceptional degree falls below k.

Combining that result with the separately proved [degree class {k,k+1}](../verify/adjacent-degrees.md), every qualifying graph whose maximum and minimum degrees differ by at most one now has a spanning path. Indeed if the smaller degree is attained at least twice, the graph belongs to the latter class; if attained only once, all its other degrees are k. No order or connectivity restriction remains for this conclusion.

Without an assumed degree bound, in a hypothetical counterexample every exterior u touching a longest path starting at the selected z, with marks W as above, satisfies

    |W|(n−3k−1) ≤ k Σ_{w∈W} [d(w)+e(w)−d(u)−d(s(w))].

This follows by summing the wedge inequality before discarding the degree terms and using the defect sum ≥|W|. In particular when n>3k+1 some mark has degree strictly greater than d(u); and the mean degree of the marks is at least d(u)+(n−3k−1)/k. All the successors are high and e(w)≤k. The graph arguments were independently reviewed.
