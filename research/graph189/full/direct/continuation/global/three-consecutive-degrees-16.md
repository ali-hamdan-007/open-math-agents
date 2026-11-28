# Lowering the three-degree threshold to 16

The theorem of three-consecutive-degrees.md also holds for every k≥16. Use the same notation and suppose κ≥3, n≤5k+1. Below are replacements for the estimates requiring k≥65.

## Hamilton-connected routing in the whole exterior component

This step works for all k≥6. Suppose C is two-connected, let x minimize q=deg_C(x), and put b=|C|. If b≥2q, a cycle of length at least 2q follows from Dirac. Three connectors give n≥b+6q+5, counting all of C in addition to two tails of ≥2q and both gaps of ≥q+1. Thus 8q+5≤5k+1. Put X=N_C[x] and let R consist of all y∈C at ambient distance two from x. All one-vertex exchange middle vertices are high, so the optimized shift bound gives r=|R|≤2q−k. Since q≤(5k−4)/8≤k−2, r≤q−2 and b≥2q forces I=C−(X∪R) nonempty. There are no X–I edges. Every vertex of I has at least q−r neighbors in I.

Put a=2k−3q≥(k+12)/8>2. By the proof of two-thirds-exterior-degree.md all members of X have ≥k−q neighbors in X. Thus X is Hamilton-connected since 3q≤2k−2. Each of its vertices has ≥k−q−r≥a path contacts, so match a of them. In the route replacing an outer tail, any prescribed X-port v can be first on a path using all X and at least q−r+2 further C vertices. Indeed C−v is connected, so there is a path from X−v to I avoiding v. Trim it to its last X vertex w and first I vertex y, with at least one R vertex between them. Traverse X from v to w, then the trimmed connector to y, then a rooted path on ≥q−r+1 vertices in I starting at y (end a maximal path and count end-neighbors). Thus both tails count ≥q+1+k−q+2, besides the intervening gaps of ≥q+1 from X. It follows that

    5k+1 ≥ n ≥ b+a+(a+1)(q+1)+2(k−q+2)
                    ≥ (a+1)q+2a+2k+5.

Substituting q=(2k−a)/3 gives (2a−7)k≤a²−5a−12. If a≥4, then k≥2a by q≥k/2, but 2a(2a−7)−(a²−5a−12)=3(a²−3a+4)>0. If a≤3 it must equal 3, implying k≤12 by a≥(k+12)/8 while the last inequality forces k≥18. Consequently b≤2q−1, and C is Hamilton-connected.

## A cut vertex in C is impossible at k≥16

Let B be the all-high endblock, w its sole articulation, b=|B| and q the least internal degree among its noncut members. These degrees equal their C-degrees. Write h=ceil(k/2), so |C−B|≥h. If b≥2q−1, Fan's theorem supplies a cycle of length L≥2q−1. Three connectors give n≥b+h+6q+3≥8q+h+2. Thus a=2k−3q≥(k+3h+3)/8≥6. For a minimizing noncut x the same optimized full X and a contacts exist, using the path witness proof for all neighbors, even the articulation. Thus n≥(2q−1+h)+a+(a+1)(q+1)=(a+3)q+h+2a>5k+1.

If b≤2q−2, B−w is Hamilton-connected by its minimum degree ≥q−1. There are t=max(2,k−b+1) distinct matched B−w contacts, by the degree and connectivity arguments. As in the companion each tail extends from its prescribed port through all of B, then through a rooted path on ≥h vertices in R=C−B. Hence n≥(t+2)b+3h+1. For b≥k−1 this is ≥4(k−1)+3h+1>5k+1. For h+1≤b≤k−2, b(k−b+3) is concave; at b=k−2 its value is 5k−10, and at b=h+1 it is (h+1)(floor(k/2)+2)≥(k/2+1)(k/2+3/2)>5k for k≥16. Adding 3h+1 therefore gives the contradiction throughout.

## Exact residual sizes and three marks

C is now Hamilton-connected. As in the companion, a matching of p≥max(3,k−m+1) contacts with m=|C| implies n≥(p+2)m+p; and m≥h+2. For h+2≤m≤k−3 this concave lower bound at m=k−3 is 6k−14>5k+1 for k≥16. At m=h+2 it is (h+2)(floor(k/2)+1)+floor(k/2)−1>5k+1 (at k=16 both sides are 97,81 respectively; the gap increases for both parities). Hence m=k−2 or k−1, and 6m+4>5k+1 excludes a four-matching.

In the finite bound of the companion, each of at most two external penultimate vertices has an L₁(w)-neighbor on its geodesic, so gives at most k+1 distance-three vertices. One mark of A' already neighbors w. Hence the sharpened bound on |V−C| is 1+(k+2)+2+2(k+1)+|A'|−1=3k+6+|A'|. This contradicts 4m+3 for m=k−2 with |A'|=3 and m=k−1 with |A'|≤6 at k≥16.

Finally in the three-mark m=k−1 case, let X_i consist of the members of X adjacent to the ith mark alone. Suppose no C vertex meets all marks and no mark meets all of C (the latter already gives the finite contradiction). Since all C vertices have at least two contacts, each misses exactly one and all three miss classes are represented. For each i take a C member missing mark i. It sees X−X_i and Z at positive even distance. From |V−C|≥4m+3 we derive 4m≤|Y|+k+|X_i|. Each of the m missed mark incidences counts in the marks' even budgets, so |Y|+m≤3k. Consequently |X_i|≥5m−4k=k−5 for each i. These three sets are disjoint and |X|≤14 as established in the companion, which is impossible already at k≥10. Thus a C vertex complete to A exists and the remainder of the companion proof applies.
