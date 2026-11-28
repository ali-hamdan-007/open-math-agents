# Exact maximum-root width with both column deficits retained

For a maximum-degree root x put d=Δ=k+e and let C be the high vertices in L₃(x). Define the integer width w=ceil((2(n−2k)+ke)/(k+1)). The following is necessary:
    w|C|≤kd+k max(0,k−w),      |C|≥n−d−k−2.
In particular, if w≤k and w>0 then w(n−d−2)≤k(d+k).

Write A=N(x), B=L₂(x). For each a∈A write p_a=|N(a)∩B|. Then a is nonadjacent to exactly d−d(a)+p_a≥p_a of the other members of A, all even witnesses at distance two through x. Thus a has at most k−p_a slots for distinct C vertices at even distance.

For each y∈C fix a three-step geodesic x,a(y),b(y),y. Its two common-neighbor counts sum to at least w by the two-ended wedge inequality, retaining degrees and using d(y)≥k. Summing the first count over y costs ≤dk−∑p_a: each of its witnesses a'∈A is at distance two to y through b(y).

Let B' consist of b∈B with at least one C neighbor. Write h_b=|N(b)∩A|, M_b=max{p_a:a∈N(b)∩A}. Every C neighbor of b is at distance two to every such a, so b has at most k−M_b C neighbors. Also h_b+M_b≥w: choose a∈N(b)∩A and y∈N(b)∩C. On x,a,b,y the first co-degree is h_b and the second is at most p_a since all its witnesses are in B. The second width count charged over the chosen y costs at most the number of edges from B' into C, hence at most ∑(k−M_b).

Combining and using ∑p_a≥∑_{B'}h_b gives w|C|≤dk+|B'|(k−w). Since |B'|≤|B|≤k, the claim follows. The argument only uses the definition of Δ and the high–high distance-three wedge bound, plus the standard count for |C| from the even cap and the unique possible low. It applies whether x is adjacent to the low vertex or not.

## Cancellation of the full second-layer term

In fact w(|C|−k)≤kd always, and w|C|≤kd if all members of A are high.

Let C' consist of those y∈C having a geodesic from x whose first neighbor belongs to A and is high. For each choose such a geodesic; let B' now be all columns adjacent to some C' member and having a high first-layer predecessor. Every column charged in the second co-degree through a chosen path has the chosen high first neighbor as a predecessor and hence belongs to B'. If y∈C−C', the unique possible low vertex in A has distance two to y. Thus |C−C'|≤k; if no low belongs to A then C'=C.

For each b∈B' choose one high A-neighbor u. Its closed neighborhood within A has exactly d(u)−p_u≥k−p_u members, all at distance at most two from b. At most h_b of them are adjacent to b. Consequently the number of even incidences (a,b), a∈A, is at least max(0,k−p_u−h_b). These are debits on the same cap at a as before, disjoint from the missing-A-neighbor debits and from C'. Summing over b counts distinct such pairs. The overall sum bounding w|C'| is now at most
    kd + ∑_{b∈B'} [ k−h_b−M_b−max(0,k−p_u−h_b) ] ≤ kd
since M_b≥p_u. This proves both assertions.

At n>3k+1 even the possible low loss disappears. If A contains a low z and b∈B has no high first-layer predecessor, then N(x)∩N(b)={z} and x,b are high. The induced wedge x,z,b has defect J≥1, whereas d(z)+E(z)−d(x)−d(b)≤−1. The wedge order inequality gives n≤4k+2−k−(k+1)=2k+1, a contradiction. Thus every b∈B has a high predecessor, every y can use a suitable geodesic, and
    w(n−Δ−k−2)≤kΔ.

## Integer width from both matched wedges

The matching-based wedge inequality in ../verify/wedge-penultimate-matching.md yields a sharper three-step width. Put f(t)=t(k−t−1), and define F(K)=max{f(t₁)+f(t₂)+ε₁+ε₂ : tᵢ≥0 integer, εᵢ∈{0,1}, Σ(tᵢ+εᵢ)≤K}. For a geodesic from Δ to a high y, with two common-neighbor counts summing to D, one has
    K=D−2−e≥0,        2n≤6k+D+F(K).
Indeed the sum of the two wedge defects is at least 4−D and the sum of the two degree/even excesses is at most −e. Thus the available penultimate capacities sum to at most 2−e−(4−D)=K. Summing the two local matched wedge inequalities gives the order bound.

At K≤k−3, F(K)=f(floor(K/2))+f(ceil(K/2)): the optimum balanced distribution follows by discrete concavity, and replacing an epsilon unit by the next unit in a balanced available row gains at least one. This gives a monotone necessary minimum integer D via the exact finite two-wedge inequality. One may use both this and the earlier linear width lower bound in the complete column cancellation.
