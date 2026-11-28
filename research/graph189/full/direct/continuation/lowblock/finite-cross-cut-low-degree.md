# Finite bound on the deficit of a low vertex belonging to a minimum cut

Let a hypothetical counterexample have order n, second-smallest degree k, connectivity s, maximum degree k+e, and unique low vertex z of degree k−d<k belonging to a minimum cut S. Let A,B be nonempty complementary groups of components of G−S, with |A|=X≤|B|. Both are wholly high and each anchor touches both. Select a neighbor a∈A of z and b∈B of z. Put r=|N(a)∩N(b)|; this intersection is contained in S, so 1≤r≤s. Then
    kd ≤ 2k+(k+1)r−n,    d≤r−1,
    (r−1)(k−s+1) ≤ (s+1)k−n+X+s + r(e+s−1).
These inequalities also hold at smaller orders; no asymptotic assumption enters. To bound X test X(n−s−k−X)≤sk² and X≤floor((n−s)/2), by the finite cross population theorem.

The first bound is the wedge order inequality at a,z,b: its defect is at least 2−r and its excess is at most −d. For the second, N[a] and N[b] intersect in just their r common neighbors since a,b are nonadjacent. Their union lies in the closed two-ball of z, of size ≤1+k−d+k. This gives d≤r−1.

For the final bound put T=N_S(a) and L=N_S(b), and write E_i=R_i=N_B(Q_i)−Q_i for i∈T, E_i=Q_i=N_B(i) otherwise. Each |E_i|≤k. Any B point at odd distance from a has distance three and lies in the union of these windows, by the one-sided geodesic argument. Its available even quota in B is ≤k−s+|T|: the full exterior boundary of N_A[a] has size ≥s since it separates a from B, and all its members except the |T| adjacent anchors are at distance two from a outside B. Hence the exact mixed debit
    F=Σ_i(k−|E_i|)+Σ_{x in union E}(multiplicity(x)−1)=sk−|union E_i|
is ≤(s+1)k−n+X+|T|, using |B|=n−s−X.

Put W=N_B[b], of order ≥k−|L|+1. For i∈T∩L it is contained in Q_i∪R_i. The closed A-neighborhood of high a leaves at least k−|T|+1−p_i even witnesses of i outside its A contacts, p_i=|N_A(i)|. Hence |R_i|≤p_i+|T|−1, while p_i+q_i≤k+e from its ambient degree. Thus q_i≤k−|R_i|+e+|T|−1. Summing covers of W over the r common labels gives
    (r−1)|W|≤F+r(e+|T|−1):
the q_i are paid by the displayed R deficits, and repeated R memberships inside W are paid by their disjoint debit terms. Substituting |T|,|L|≤s proves the formula.

The helper cross-cut-filter.py uses integer bisection for the maximum possible smaller side, the proven retained-width inequality at the maximum-degree root, and these inequalities to return the largest permitted d. When it returns zero, either a genuine minimum lies on no minimum cut, or the minimum is tied. In the former case the universal-minimum-order theorem gives n≥(s+2)(k−s+1)−1, and in the latter the same holds when the critical deletion and exterior-cycle conditions are met. For positive d, if the critical-connectivity threshold holds, making the removable vertex universal gives minimum at least k−d and connectivity s+1; the order lower is then (s+2)(k−d−s+1)−1, subject to the already proved independent-exterior exception and that the surviving outside cycle has order ≥s+1. The finite runner conservatively checks those prerequisites.

## Direct uniform barrier at s≥100

In the residual k>5s, suppose s≥100. The necessary universal order gives n≥(s+1)(k−s+2)−1>0.8sk. The degree-k-root bound gives n<2k+2+k sqrt(k+1), hence sqrt(k+1)>0.8s−2.01 and k≥0.59s² (for s≥100 the inequality follows already at 100 and its proportional slack increases). We then have n≥(s−1)k, since 2k−s²+s+1>0. Since δ may be low only on S in the current case, one can use the smaller of two high groups with X≤(2+8/s)k≤2.08k, by the finite population theorem; k>6(s−1) also ensures there are just two components.

Write m=n−2k. As e≤4k, m−e−2≥(s−8)k. The retained-width inequality implies (s−8)e≤(1+1/k)(2k+e), so e≤2.03k/(s−10). In the genuine low-on-cut case F≤sk−|B|+k≤s²+X≤3.78k using the full n lower and k≥0.59s². The common-label inequality in its proof form gives
    r≤(F+k−s+1)/(k−2s+2−e) <6.
Indeed e/k≤2.03/90 and 2s/k≤2/(0.59*100). But the first displayed low wedge inequality gives r≥(n−k)/(k+1)≥s−3. There is no such low on a minimum cut.

Use the lifted order n≥(s+2)(k−s+1)−1. In the all-high case a removable vertex exists by the critical-connectivity theorem since k≫s; the independent-exterior alternative would give n≥k(k−1)/4, contradicted by n≤2k+1+sqrt(k²(k+1)+1) throughout k≥5900. The surviving high outside cycle has length ≥s+1 as k≥4s+4. For an actual low outside every minimum cut the lifted universal completion is immediate. Combining with the three-common-label order upper n<(s+1+3/(s−2))k+2s+3 gives
    k≤(s²+3s+2)/(1−3/(s−2))<1.08s².
The high-order rooted local Ore upper n≤3k+1+(k−2)e and n≥(s−1)k force e≥s−5. The sharper upper e≤2.03k/(s−10) then gives m−e−2≥(s−4)k, 2m+ke≥(3s−11)k, 2k+e≤2.03k. Using retained width now yields (s−4)(3s−11)≤2.03(k+1), which for s≥100 implies k>1.35s², a contradiction. Thus s<100 uniformly. This is an alternative to any independent finite global cutoff.
