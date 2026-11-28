# Three common labels at arbitrary arity

At connectivity s≥5 and second-smallest degree k>6(s−1), every qualifying graph is traceable when

    n ≥ (s+1+3/(s−2))k+2s+3.

Together with arbitrary-cut-high-order.md one may use the better of this bound and (s+3/2)k+2s+2.

Assume the displayed high order in a counterexample. Use X≤Y, H=X+Y, A,B,S as in arbitrary-cut-high-order.md. Then H≥(s+1+3/(s−2))k+s+2. At x=X/k with x≥s/(s−2), the convex f(x)=x+1+s/x on the interval ending at (1+sqrt(1+4s))/2 has maxima at its endpoints. At s/(s−2) the value is s+2/(s−2); at the other endpoint it is 1+sqrt(1+4s)<s+1 for s≥5. Neither reaches H/k, which must be ≤f(x). Thus X<sk/(s−2) and Y>sk.

The high contact at every label, exclusion of high A nonports by private A contacts, and the support-family description all follow as in arbitrary-cut-high-order.md. In particular the edge-order lower bound still gives at least s−1 common neighbors because n>(s+1)k+2s. For the all-private case the bound H≤sk+(1+1/s)X+1 is now strictly less than sk+(s+1)k/(s−2)+1. This excludes that case under the present order. In the remaining families c counts the common labels, d=s−c, and the counts P_C,P_D,G and Q_G are as in that paper. Residual singleton sets yield

    P_C+P_D+G ≤ dk+Q_G/d,     Q_G ≤ X+d(c+1).

At c=1 or 2, X≤k and d≥s−2, so the upper H≤sk+(1+1/(s−2))k+c+1 contradicts the assumed high order. The c=0 case is the previously excluded private family. Any co-singleton family at d≥3 gives Y≤sk. Consequently every minimum cut has c≥3; we no longer need c≥s−1.

Every such cut has a high private B port on a common label. As in six-cut-large-degree.md, assume otherwise and at most one common label can be the sole exact-distance-two label of a high B nonport, by use of the private predecessor and the single possible low vertex. If there is a high full A port, it covers P_C+P_D and all high B depth-three vertices. The high B depth-two population has ≤(d+1)k singleton-nearest members. Its other members require two anchor incidences. Thus Y≤k+(s+d+1)k/2≤sk since c≥3, contradiction.

In the absence of a high full A port, d≥2 and the remaining support family is the residual singleton family. Let H_C be the number of high B nonports with at least one common exact-two label. Bound its doubles at the common and residual anchors, with at most k solely nearest to the one exceptional common label; hence 2H_C≤ck+Q_C+k, where Q_C counts residual exact-two incidences on these nonports. Moreover the same high A windows give Q_G+Q_C≤X+d(c+1)≤k+d(c+1). The singleton bound above and d≥2 now yield

    Y ≤ dk+(c+2)k/2+d(c+1)/2 < sk.

The strict inequality is equivalent to (c−2)k>d(c+1), following from c≥3 and k>6(s−1). This proves the existence claim.

For X≥k−s+1 this high private B port v sees at least k−s+1 high A members at distance two. If X=k−s instead use the same singleton-low adjustment as in arbitrary-cut-high-order.md: every high A member is full and complete in A; a low nonport has opposite parity to all B vertices from a full high member. If the low is a port, all labels have a singleton-nearest high B member as Y>sk, and a suitable private representative on that label sees all of A. A smaller X is impossible by degree. Thus W=N_B[v] has ambient boundary ≤s. In the high full-port case there are ≤k high B ports. In the residual singleton case the d representatives cover all B ports, giving ≤dk. At most k high B nonports belong to W. Since c≥3, the remaining high population outside W and its boundary exceeds (c−1)k−s≥2k−s in the latter case (and exceeds (s−2)k−s in the former), larger than sk/(s−2). Hence ∂W is a minimum cut, W is its smaller side, and the high v has only one contact on it, contradicting the uniform c≥3. This completes the direct order proof.

## Sharper connectivity consequence using the common-neighbor count

If a minimum-degree vertex z belongs to a minimum cut and δ(G)<k, take high neighbors a,b of z on opposite sides. Their open neighborhoods meet in S, and neither contains a or b. The union of those neighborhoods, a and b lies in the closed radius-two ball about z. Therefore

    1+δ(G)+k ≥ 2k−|N(a)∩N(b)|+2,     δ(G)≥k−s+1.

If δ(G)=k the latter bound is immediate. This sharpens the low-anchor degree step in critical-removable-vertex.md. Making a removable vertex w universal now gives δ(K)≥k−s+1 and κ(K)≥s+1. The same nonindependent-exterior shift proof in H=G−w yields internal minimum degree at least ceil((k−2s)/2), and hence an exterior cycle of size ≥s+1 when k≥4s. Its Nikoghosyan order lower bound becomes

    n ≥ (s+2)(k−2s+2)−1 = (s+2)k−2s²−2s+3.

For the independent alternative the previous n≥k(k−1)/4 is stronger than the required order whenever k≥6(s+2). If a minimum-degree vertex belongs to no minimum cut the already proven order bridge is stronger still. Thus the direct order theorem implies unconditional traceability, for example, whenever s≥6, k≥6(s+2), and

    (1−3/(s−2))k ≥ 2s²+4s.

For s→∞ this gives liminf s/sqrt(k)≥1/sqrt(2) in any sequence of counterexamples. The earlier finite bounds remain available for small s. When combined with the independent universal upper order bound, any residual growing-connectivity sequence lies entirely in the square-root scale.
