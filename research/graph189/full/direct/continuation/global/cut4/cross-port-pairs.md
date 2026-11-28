# An aggregate bound for ports on opposite sides of a separator

Let S be a separator of size s in a qualifying graph, and let A and B partition the components of G−S into two nonempty groups. Assume each anchor touches both sides, as happens for every minimum separator when A and B are components. Call a vertex high when its ambient degree is at least the second-smallest degree k. There is at most one other vertex. Call a vertex outside S a port if it has a neighbor in S.

Let p_A,p_B be the numbers of high ports and let E count pairs (i,x) with i in S, x a high port and d(i,x)=2. Put a=min(p_A,p_B) and b=max(p_A,p_B). Then

    (1)    ab ≤ ka + kE.

Indeed each anchor has at most k port neighbors on either side, by measuring at an opposite neighbor of that anchor. Every cross pair of high ports is at distance between two and four by the established high-pair diameter theorem. At most ka pairs have even distance by summing the caps on the smaller side. A pair at distance three has a separating anchor at distance one from an end and two from the other. Counting by the latter incidence, the former end has at most k choices. This proves (1).

For a high nonport x let J(x) be its set of anchors at distance two. Summation of the s anchor quotas gives

    (2)    E + Σ_x |J(x)| ≤ sk.

Both inequalities are independent of the number of separator vertices.

## The four-cut with high nonports on both sides

Suppose s=κ(G)=4, k≥32, and each of the two components of G−S contains a high nonport. Then G is traceable. Previous order theorems allow us to suppose n≥6k−10, and minimum-cut-two-sides.md ensures there are exactly two components in this range. By order/four-cut-small-deep-side.md and residual-distance-types.md, each side has order ≥2k−3 and every high nonport x has |J(x)|≥2. Each side has at most k−4 high nonports, since every one is in the fourth layer from an opposite high nonport, whose second layer separates it from them and contains at least four vertices. Even allowing one low vertex, both port counts are at least k. Both are at most 4k by summing the contacts of the anchors.

If d is the total number of high nonports, (1) and (2) give

    n ≤ 5+a+b+d ≤ 5+2k+a+b−a(b−k)/(2k).

When a≤2k this upper bound is increasing in b; using b≤4k yields n≤5+6k−a/2≤5+11k/2. When a≥2k it is nonincreasing in b; using b≥a and maximizing the quadratic yields n≤5+2k+25k/8=5+41k/8. Thus n≤6k−11 for k≥32, a contradiction.

For use when one side is shallow, the directional version also charges high nonports y in B from high ports x in A whose support misses J(y). For a high depth-two y, all such x have distance four. Consequently p_A p_B plus the sum over y of the number of such x is at most k p_A + kE, with no duplication between the two types of pair.
