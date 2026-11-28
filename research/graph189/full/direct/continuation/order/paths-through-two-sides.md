# A long path through two arbitrary wholly high sides of a minimum cut

Let S be a minimum cut of size s≥3 with precisely two components C,D outside it. Assume that C,D are wholly high, and put d=k−s≥2. Write m₁,m₂ for their orders and o for the number among these two components that are not 2-connected. There is a single path in G on at least

    1 + min(m₁,2d) + min(m₂,2d) + o

vertices. This part uses only the degree and connectivity assumptions. In particular it does not assume that all anchors have many contacts, or that the sides have bounded order. Every member of a side has internal degree at least d, and both sides touch every anchor by minimality of S.

First suppose a side H has a cut vertex. Pick any two distinct leaf blocks B₁,B₂ of H. Each has a unique articulation w in H; all other vertices in the block have at least d neighbors in that block. No leaf block is a bridge, since a leaf bridge's noncut vertex would have degree one in H. At least s−1 distinct anchors have neighbors in the noncut part of each leaf block: deleting those anchors and w would otherwise disconnect the nonempty noncut part from the opposite side with fewer than s deletions.

For any prescribed noncut vertex p of a leaf block B of order b, there is a p-to-w path of at least d+1 vertices in B. If b≤2d−1, add a marker joined only to p,w and apply cycle closure. The degree sum of any two original noncut vertices is at least 2d≥b+1, so closure completes them to a clique. The articulation has at least two neighbors in the 2-connected B, so in the closure a path starting at p through the whole noncut clique can end at a neighbor of w distinct from p. Together with w and the marker this gives a spanning cycle, whose existence survives reversing closure. Deleting the marker gives a spanning p,w-path, and b≥d+1. For b≥2d use Fan's circumference theorem at threshold 2d: every distance-two pair in B contains a vertex other than w and thus one of degree at least d. A cycle of order at least 2d exists. By 2-connectivity, two disjoint paths from p and w to that cycle with distinct ends exist; vertices already in the cycle may use length-zero paths. Truncate the paths at their first cycle encounters. Joining them by the longer cycle arc gives a p,w-path of at least d+1 vertices.

Choose the joining anchor a as follows. For a 2-connected side any anchor is acceptable. For a side with cut vertices choose the s−1 or more anchors touching noncut vertices of its first selected leaf block. The two sets of acceptable anchors intersect because 2(s−1)>s. In a non-2-connected side, take p∈B₁−{w₁} adjacent to a and use the preceding local path, then join w₁ to w₂ by a path internal to H avoiding the noncut parts of the two leaf blocks (length zero if w₁=w₂). Finish with a long w₂-to-p₂ path inside B₂, choosing any noncut p₂. This path begins at the specified portal and has at least 2d+1 vertices. In a 2-connected side use Fan's theorem (or Dirac's circumference bound) for a cycle of length at least min(m_i,2d). Join a to it by a shortest path through that side and traverse the entire cycle by opening it at the attachment vertex. Join the two resulting paths through a. The sides are disjoint, proving the display.

For a nontraceable Graph 189 instance let M be the number omitted by a longest path. The upstream almost-spanning and exterior-size theorems give M≥ceil(k/2)+2. Counting vertices not covered by the displayed path yields

    (m₁−2d)_+ + (m₂−2d)_+ ≥ M + 1 − s + o.

At s=3 this gives ≥ceil(k/2)+o without an order assumption. The upstream near-degree exterior theorem improves M to >k−sqrt(3k)−4 for k≥432.

If n≤5k+1 and k≥24, then M≥k−2. Indeed otherwise a high-containing omitted component has order m in [ceil(k/2)+2,k−3]. The upstream exterior inequality m(k−m+3)≤n+1 applies. The quadratic is concave. At the smaller endpoint it is at least (k/2+2)(k/2), exceeding 5k+2; at k−3 it is 6k−18>5k+2. This contradiction proves the bound. In consequence at a clean three-cut in this order range

    (m₁−2k+6)_+ + (m₂−2k+6)_+ ≥ k−4+o.

If both sides have order at least 2k−6 this forces n≥5k−13+o. Otherwise the larger side must have order at least 3k−10+o. These restrictions apply also when the possible low vertex belongs to S and regardless of the maximum degree. References for the previously established omitted-component inequalities and precise external Fan theorem are recorded in ../global/near-degree-exterior.md and ../lowblock/high-connectivity-complete.md.

In fact the last displayed excess inequality and both of its alternatives hold for **every** n at a clean three-cut when k≥24: if n>5k+1, its left side is at least m₁+m₂−4k+12=n−4k+9≥k+11, already larger than k−4+o. Thus the order upper bound was needed only to sharpen the omitted-path estimate in the nontrivial range.
