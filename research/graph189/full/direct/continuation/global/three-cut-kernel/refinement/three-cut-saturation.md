# Three-cut local counts at moderate degrees

This note works with a genuine minimum three-cut, anticomplete sides A and B, and high populations X and Y, where high means degree at least the second-smallest degree k. Write x=|X|≤y=|Y|. Each anchor i has high contact sets A_i and B_i of size at most k. Every high cross pair has distance two, three, or four. These are inherited consequences of the original Graph 189 cap. The lemmas below are paper arguments. The existing Lean threshold module covers all κ=3 at k≥37.

## Private contacts on a dense side

Suppose each high vertex of A has at most one anchor neighbor and each anchor has a high representative in A. If |A|≤2k−1, then

    2x+3y ≤ 12k−12.

Each high vertex has at least k−1 neighbors in A. Two distinct nonadjacent high vertices of A have a common neighbor there, since their two neighborhood sizes sum to at least 2k−2 and their union omits both vertices. For each anchor i choose a high representative a_i. Let t_i count X in the closed A-neighborhood of a_i. All x−t_i remaining high vertices of A consume distance-two slots of a_i.

Let N be the high B-nonports, P the high B-ports, and Z_i the vertices of N at distance two from i. Every B_i vertex and every vertex of N outside Z_i is at even distance from a_i. Indeed an odd cross distance can only be three, and a geodesic to a nonport must start through a_i's only label i. The two sets are disjoint and their combined size is at most k−(x−t_i). On the other hand, all t_i vertices are neighbors of i or at distance two from i. Thus |Z_i|≤k−t_i+|A_i|. Adding cancels the dependence on t_i:

    |B_i|+|N| ≤ 2k−x+|A_i|.

Summing gives |P|+3|N|≤6k−2x since the A_i are disjoint. The ordinary per-representative minimum-cut debit independently gives |B_i|≤k−2, hence |P|≤3(k−2). Multiplying y=|P|+|N| by three proves the claim. The ordinary debit and the nonneighbor cost are applied to separate inequalities. They may overlap as sets.

## A saturated column

Suppose |A_i|=k and b is any B-neighbor of i, which exists by minimality. All of A_i lies at distance two from b. The opposite-side even debit forces b to touch all three anchors, and there is no other positive even vertex from b. Every B-vertex is b or adjacent to b. To see this, take the set of B-vertices different from and nonadjacent to b. An edge from that set to a neighbor of b, including any separator vertex, would produce a distance-two B-vertex. There is no edge to A or b, so a nonempty set would disconnect G.

The high B-nonports are at distance two from i through b, so there are at most k. Every B-neighbor of i is universal to the anchors, so the other two labels cover all high B-ports. This gives y≤3k. If either of those other two B-columns saturates, reversing the preceding universal-port argument gives a universal A-port, and then there are at most k high B-ports. In that event y≤2k. Otherwise each of the two covering labels has at most k−1 high contacts. In particular y≤3k−2 whenever k≥2.

There is also an independent obstruction when x>2k−3 and y>2k. The universal b sees all high A-ports at distance two, so there are at most k high A-ports. Their complement contains more than k−3 high nonports. A high B-nonport would see all those A-nonports at distance four, contradicting its mandatory debit of three. Therefore Y consists entirely of ports and y≤2k, a contradiction.

For a bound on the opposite population, assume |B_i|=k, x>k and y>2k−3. The universal A-contact a sees every high B-port at distance two, so there are at most k of those. Hence there is no high A-nonport. Each high A-vertex is a or adjacent to a, by the same connectivity argument. For each label j, every vertex in X outside A_j is at distance two from j through a. Each high B-nonport must be at distance two from at least one anchor: otherwise it is at even distance four from every high A-vertex, since an odd cross geodesic would have to go through a label at distance two. Its own debit would give x≤k−3. Summing the remaining three anchor budgets bounds the high B-nonports by 3k−3(x−k). Consequently y≤7k−3x. This is the three-cut version of the four-cut worker's saturation argument.

## A column short by one

Suppose |A_i|≥k−1. For every B-neighbor b of i, let E be the positive even vertices from b outside A_i, so |E|≤1. Let T be the anchors missed by b. The minimum-cut even debit at b gives |T|≤1. Since |E∪T|≤2<κ, deleting E∪T preserves connectivity, and b survives. Every B-vertex that is different from b and nonadjacent to b belongs to E. Indeed, in G−(E∪T), the remaining B-nonneighbors cannot reach b: a step to any B-neighbor of b or any surviving anchor would put its initial vertex at distance two from b, and an edge to A is impossible. Thus all but at most one high B-nonport are adjacent to b. They are at distance two from i, so there are at most k+1 high B-nonports.

In fact this argument gives a stronger ceiling. All high B-vertices outside B_i and those exceptions are at distance two from i through b; b itself is an i-neighbor. Hence y≤k+|B_i|+1≤2k+1. The exact-saturation version gives y≤k+|B_i|≤2k. More generally let t=k−|A_i| for a minimum cut of size s. When 2t<s, the identical deletion argument uses at most t exceptions E and t missed labels T. It gives y≤k+|B_i|+t. These bounds apply when the opposite contact is the unique low vertex as well.

## Concentration of the odd rectangles

Assume every A_i has at most u vertices and every B_i has at most v, with u<v, x>k. Write P for the union of the high B contact sets and N for its complement in Y. If |P|>k+v, every two B-columns have union larger than k, because the third column contains at most v vertices. No A-vertex can then touch two labels: it would see more than k high B-vertices at distance two. Thus the sum of the three A-column sizes is at most x.

Otherwise |N|≥y−k−v. Each high B-nonport has at least one anchor at distance two. Without such an anchor all of X would be at even distance by the odd cross-geodesic argument, contradicting x>k. Accordingly the sum of the three high B distance-two column sizes is at least y−k−v. In the exact odd rectangle charge, each B distance-two incidence is multiplied by at most u, and each A distance-two incidence by at most v. The combined distance-two count at each label is at most k. Thus the usual upper bound 3kv loses at least (v−u)·max(0,y−k−v).

It follows that the total bound 3u+3kv for the even contact sum plus the odd rectangles can be lowered by

    min(max(0,3u−x), (v−u) max(0,y−k−v)).

At k=25, x=35, y=75 the near-saturation and opposite-saturation estimates give u=23, v=24. The saving is at least 26. The original product slack was only 14.

## Finite pairing with the previous recut theorem

If both sides' columns have size at most k−1, the existing odd-rectangle argument uses at most 3k(k−1), because the two distance-two column sizes for each anchor sum to at most k. The even charge is at most kx−3x+3(k−1). More generally with no saturated A-column the even charge gains three, and with no saturated column on either side the odd charge gains 3k.

The accompanying script combines those counts and the previous private and residual singleton quotas with the checked lower order n≥5k−11. For k=25 through 36 no remaining population pair satisfies the tests. Combined with the previous recut implication and the kernel theorem from k≥37, this gives a **paper extension to k≥25** provided the lemmas and their assembly survive independent review. The numeric checks alone give no official or Lean verdict. At k=24,n=109 the first population pair surviving these estimates is (22,83). The argument has therefore not settled the full parent.
