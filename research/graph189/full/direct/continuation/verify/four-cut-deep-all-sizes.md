# Four-connectivity when both sides contain a high nonport

Let a minimum four-vertex cut of a qualifying graph leave two components, each containing a high vertex without an anchor neighbor. At every second-smallest degree k≥16 the graph is traceable, with no order upper bound, maximum-degree restriction, or condition on the placement or degree of the possible low vertex.

Assume nontraceability. By the verified moderate-order theorem, n≥6k−10. The small-side and large-side theorems in order/four-cut-small-deep-side.md and order/four-cut-large-deep-side.md ensure that each side has order at least 2k−3, or at least 2k−2 when the opposite side is wholly high. Each has order at most 4k−11, or at most 4k−12 when it is itself wholly high. Each side has at least one high nonport and at most k−4 high nonports, since they are all at distance four from a high opposite nonport and its second layer has size at least four. Write a≤b for the two high-port counts. Their bounds are

    k+1 ≤ a ≤ b ≤ 4k−13.

For the lower bound, a side containing a low vertex faces a wholly high opposite side and has at least 2k−2 vertices; it therefore has at least 2k−3 high vertices. A wholly high side itself has at least 2k−3 high vertices. For the upper bound, a side containing a low loses that vertex and at least one high nonport from its order at most 4k−11; a wholly high side loses at least one high nonport from its order at most 4k−12.

No port touches every anchor, and each high nonport has distance exactly two to at least two distinct anchors. These follow from the small-side bound, as in global/cut4/residual-distance-types.md. For the latter statement a sole nearest anchor makes all opposite high vertices missing it occur at distance four, numbering at most k−4, whereas the anchor has at most k opposite contacts. This bounds the opposite side by 2k−4 if wholly high and by 2k−3 otherwise, both excluded by the side-dependent lower bounds. The same contradiction excludes a universal port: it sees all opposite ports at distance two and a high nonport on its own side sees all opposite high nonports at distance four.

Let d count high nonports on both sides and let E be the number of incidences between an anchor and a high port at distance two. The four anchor budgets give E+2d≤4k. The aggregate cross-port count of global/cut4/cross-port-pairs.md can be strengthened to

    ab ≤ (k−1)a + kE.

Every cross pair is at distance two, three or four. For each root among the a high ports of the smaller group there are at most k−1 even partners in the other group. Indeed its closed internal neighborhood has an ambient boundary of size at least four. At most three of these vertices are its direct anchor neighbors, and the remainder include an own-side or anchor vertex at distance exactly two. For an odd pair of ports, a three-step geodesic passes through an anchor at distance one from one end and two from the other. For each incidence counted by E there are at most k possible opposite adjacent ports, using the budget of any contact on the other side of that anchor. These bounds prove the inequality.

Allowing four anchors and at most one exceptional low vertex gives

    n ≤ 5+a+b+d ≤ 5+2k+b+(3k−1−b)a/(2k).

If a≤2k the right-hand side is nondecreasing in b. At b=4k−13 it decreases in a, so it is at most 6k−8−(k−12)(k+1)/(2k), strictly below 6k−10 because k²−15k−12>0 at every k≥16. If a≥2k it is nonincreasing in b. Substitute b=a and take the real quadratic maximum, obtaining 5+2k+(5k−1)²/(8k), also strictly below 6k−10 because 7k²−110k−1>0 at every k≥16. Both cases contradict the order of a counterexample.
