# Five-connectivity at every second-smallest degree at least 6000

Every qualifying graph of vertex-connectivity five and second-smallest degree k≥6000 is traceable. No upper bound on maximum degree or order is required; the possible low vertex is arbitrary.

Assume otherwise. The block estimates in private-five-cut.md give n≥(20k−20sqrt(3k)−50)/3+9>13k/2+30 for k≥6000; the alternative near-Hamilton-connected block bounds also exceed 13k/2+30. The first strict inequality follows from k/6−(20/3)sqrt(3k)−113/3>0 at 6000 and its increase thereafter. Every minimum five-cut S splits into exactly two components. Let A be its smaller high side, X its high population, B the other side, Y its high population. The cross product gives X<6k/5, hence Y>5k. Every high member of A is a port, and every label has a high A contact, by private-five-cut.md. As there, for any two high A supports T,U, the differences satisfy |U−T|≤1. This follows from the five-root cover of B and works for nonadjacent A vertices. All statements are uniform over the choice of minimum cut.

Let C be the intersection of all high A supports, c=|C|, and let D=S−C, d=5−c. After removing C the remaining supports cover D and have empty intersection. By the elementary family lemma in private-five-cut.md, when d≥2 either all residual supports have size at most one or the family consists of all d sets D−{i} and optionally D itself. Indeed if the empty residual occurs all other residual sets have size at most one. Let P_C count high B ports touching C, let P_D count the other high B ports, and let G count the high B nonports whose exact-distance-two labels include none of C. The remaining high B nonports number at most ck by summing the common anchors' even quotas. For y counted in G let J(y) be its subset of D at distance two. A high port with support T sees y at distance four whenever J(y) misses T: a path of length three to a nonport must first go to an incident anchor at distance two from y. This observation also covers high vertices with no distance-two anchor.

In the first family, select one high A representative with residual support {i} for every i in D. These d roots see all P_C ports d times, all P_D ports at least once, and every y in G at least d−|J(y)| times. Write Q=Σ_G |J(y)|. Hence

    dP_C+P_D+dG−Q ≤ dk.

At anchor i its high representative has ≥k−c−1 high members in its closed internal A-neighborhood, since it has only c+1 anchor contacts. Apart from high A contacts at i, each such member is at distance two from i. Summing the d anchor budgets and using that each high A member has at most one residual label gives Q≤X+d(c+1). Also P_D≤dk by summing individual contact classes. Thus

    Y ≤ ck+P_C+P_D+G ≤ 5k+X/d+c+1.

If c=0 this implies n≤5k+6X/5+7≤6.44k+7. If c>0 then X≤k by a B contact at a common label; for d≥2 this gives n≤6.5k+11. Both contradict the lower order.

In the second family use a representative with residual support D−{i} at each i. Each high C-port in B (counted by P_C) is seen d times and each D-only port at least d−1 times. Let G_1,G_0 count y in G with |J(y)|=1,0 respectively. They are seen respectively at least once and d times. The d anchor budgets also give 2G≤dk+G_1+2G_0. Consequently

    dP_C+(d−1)P_D+G_1+dG_0 ≤ dk,
    2(P_C+P_D+G) ≤ 2dk−(d−2)P_C−(d−3)P_D−(d−2)G_0.

If d≥3 this gives Y≤5k. For d=2, absence of the full support means the preceding singleton case applies. If the full support occurs, a high universal A port sees every B port, so P_D≤k. The last bound now gives Y≤5k+k/2; since c=3, X≤k, again impossible. We have proved that for every minimum five-cut, c≥4. Each such cut has a high A vertex adjacent to all five labels: for c=4 the fifth label has a high contact; for c=5 this is automatic.

Fix such a cut. Let u be a full high A vertex. Every variable below counts high B vertices. The ports and depth-three vertices together number at most k, since u sees them all at distance two or four. The high-pair distance bound ensures no high B vertex has depth greater than three. Every label i has a high B depth-two vertex whose unique nearest label is i: if some such class is absent, the other four anchor quotas cover every depth-two vertex and give Y≤5k. Consequently each i has a private B contact v_i on a geodesic to its singleton-nearest class. These contacts at distinct labels are distinct. We seek a high v_i on a common label seeing ≥k−4 A vertices at distance two.

If X≥k−4, at least one of the four or more chosen common-label contacts is high, and it sees all X high A vertices. Otherwise X=k−5: indeed |A|≥k−4 by any high member's degree, and at most one low is available. Thus A contains the low z, |A|=k−4, all its high members are adjacent to every possible neighbor in A and S, and all B vertices are high. If z has an anchor neighbor i, then v_i sees all of A, providing the required k−4 vertices. If z has none, it has distance exactly two to every anchor, hence distance 2+depth(y) from each B vertex y. Meanwhile u has distance 1+depth(y). The opposite parities give |B|≤2k, impossible.

Fix the resulting high private B port v on label i. Its closed internal B-neighborhood W=N_B[v] is connected. Every vertex of its ambient external boundary is i or is in B∪S at distance two from v. Indeed i is the only outside neighbor of v, neighbors of the internal neighbors of v cannot lie in A, and all W members are in B. As v sees ≥k−4 separate A vertices at distance two, its entire external boundary has size at most five.

There are more than 6k/5 high vertices outside W and its boundary. In fact Y>5k, at most k of its members are ports, and among the high B nonports at most k can belong to W, because those in W are at exact distance two from i. Even after deleting five boundary vertices, more than 3k−5 high B vertices remain. Thus the boundary is a cut; connectivity forces its size to equal five. In this new minimum cut W constitutes one component and is its smaller high side, since the opposite group exceeds the universal smaller-side bound X<6k/5. But v is a high member of W and its only neighbor on the new cut is i. This contradicts the established fact that at least four labels are shared by every high member of the smaller side of every minimum five-cut. The contradiction proves traceability.
