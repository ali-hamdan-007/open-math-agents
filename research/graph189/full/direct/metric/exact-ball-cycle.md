# A one-unit relaxation of the ball-degree condition

Let G satisfy the Graph 189 metric and degree hypotheses, be 2-connected, and have n>3k+2. Put s(w)=|N₂(w)|. Assume that every induced wedge u–w–v satisfies at least one of these inequalities:

- d(u)+d(v)≥|N(u)∪N(w)∪N(v)|.
- d(w)+s(w)≤d(u)+d(v)+1.

Form D on the vertices w with d(w)+s(w)≥2k+1, joining precisely pairs at distance two in G. If D is a forest then G is Hamiltonian. This local condition uses the actual size of each ball, allows one unit more than the classical ball-degree hypothesis, and does not assume balls are 2-connected.

**Proof.** Every wedge is L₁. The first inequality gives L₀; under the second one any failure of L₁ forces its three-neighborhood union to coincide with B₂(w), contrary to the wedge-cover parity lemma. At a unique-common wedge L₀ is impossible because Q contains both endpoints, so the second inequality must hold. The argument in irregular-center-cycle.md gives |M|=1 and
$$
 d(w)+s(w)=d(u)+d(v)+1.
$$
Since s(w)≤k, the unique low z (if any) cannot be such a center. Therefore w has degree ≥k. The equidistant remote set T still has size at least two. Choose t∈T with degree ≥k. The reduced target's already established lemmas five_endpoints and diameter_le_five imply that two vertices of degree ≥k have distance at most four; hence the common odd distance from t to w must be three. The sole second-layer neighbor b of t, and a high vertex a∈N(w)∩N(b), are then obtained exactly as in irregular-center-cycle.md. Specifically, a low singleton N(w)∩N(b) would itself center a unique-common wedge, which was excluded. The new wedge a–b–t has a unique common neighbor and its endpoints have degree ≥k, so d(b)+s(b)≥2k+1. Its missed point differs from w. Iteration gives an arbitrarily long immediately nonbacktracking walk in D, impossible for a finite forest. ABHV Theorem 7(a) finishes once unique-common wedges are excluded. ∎

The earlier stronger numerical assumption with k in place of s(w) also forces s(w)=k at every unique-common center. It consequently allows using the smaller D consisting of saturated above-k vertices only, via irregular-center-cycle.md.

Sources: upstream reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R1.lean, lemmas five_endpoints and diameter_le_five; Asratian–Broersma–van den Heuvel–Veldman https://ris.utwente.nl/ws/files/6633608/Asratian96on.pdf
