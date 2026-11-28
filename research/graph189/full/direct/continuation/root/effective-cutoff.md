# An explicit absolute cutoff before finite parameter enumeration

Write s for vertex connectivity, k for the second-smallest degree, n for order and Δ for the maximum degree. In any remaining counterexample,

    s ≤ 63,    k < 4s²+8s−2,    n ≤ 2k+1+floor(sqrt(k²(k+1)+1)).

The parameter files on this branch lower these conservative cutoffs by exact scalar tests. This note gives an independent elementary upper limit for those finite loops. It uses the separately reviewed lower order from ../order/complete-small-side-and-cone.md at its original k≥25s threshold.

**Maximum degree.** In any qualifying graph Δ≤3k. Put N=N(x) at a vertex of degree Δ. For u∈N the members of N outside N[u] all have distance two from u via x, so |N∩N[u]|≥Δ−k. If v is at distance two from x, choose a predecessor u. Every point of N∩N[u] is either adjacent to v or at distance two from v. Hence |N(v)∩N|≥Δ−2k. Any y in the third layer adjacent to this v sees all these points at distance two; if the third layer is nonempty this proves Δ≤3k. If it is empty, the root has eccentricity at most two. A vertex of degree k then is x, in N, or in the second layer; its neighborhood bounds from the same argument give Δ≤3k. For v∈N note that the point v itself counted in N∩N[v] is offset by its neighbor x outside N.

Suppose s≥64 and G is a counterexample. By the one-fifth connectivity result k>5s. The known bounds n≥(s+1)(k−s+2)−1 and n≤2k+1+sqrt(k²(k+1)+1) imply
    (4/5)s ≤ n/k ≤ sqrt(k)+3.
Consequently k≥s²/2 (for s≥64 use 4/5−3/64>1/sqrt(2)). Substituting back in the same lower bound gives n/k≥s−2, whence k≥(s−5)²≥25s. The completed-small-side theorem therefore gives n≥(s+2)(k−s+1)−1. The three-common-labels upper gives n<(s+1+3/(s−2))k+2s+3. Comparing the two and rounding conservatively gives
    (1−3/(s−2))k < s²+3s+3,
so k<1.105s² for every s≥64 (the relative right side and inverse prefactor are largest at 64).

Use m=n−2k and e=Δ−k in maximum-degree-width.md. The easier bound Δ≤5k, already enough for this estimate, gives m−e−2≥(s−9)k and e≤6(k+1)/(s−9)≤0.11k. Here k≥(64−5)², so 6(1+1/k)/55<0.11. The rooted wedge order implies e≥s−6, since (k−2)e≥n−3k−1≥(s−5)k−1. It follows that
    (s−9)(3s−14)k² ≤ (m−e−2)(2m+ke)
       ≤ k(k+1)(2k+e) < 2.12k³.
At s≥64, (s−9)(3s−14)/s²≥55·178/64²>2.38. The preceding inequalities would imply k>2.38s²/2.12>1.12s², contradicting k<1.105s². This proves s≤63. The explicit k cutoff follows from ../global/arity/three-common-labels.md and its degree dichotomy; the fixed-order upper holds under the original even-distance hypothesis.
