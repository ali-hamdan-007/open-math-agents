# An order bound at a connected three-vertex cut with two deep sides

Let S be a minimum separator of size three in a qualifying Graph 189 graph. Suppose G−S has two components, each containing a high vertex with no neighbor in S, and suppose the induced graph on S is connected. Then n≤4k+1, with no restrictions on the maximum degree or the placement of the possible unique below-k vertex. This fits the previously established moderate-order traceability range when κ=3 and k≥13.

Every high nonport (a vertex of a component with no neighbor in S) is at distance exactly two from S. Indeed its distance to an opposite high nonport is at least four and at most four by the high-pair diameter theorem. Each term of a four-edge path through S on the two sides thus has length two. For any vertex odd to all three anchors in S, the three distances must equal one another: they are odd and consecutive distances along edges of the connected S differ by at most one. Consequently the only exterior vertices not positively even from any anchor are the ports adjacent to all three anchors (universal ports) and at most the one low nonport.

If universal ports occur on both sides, the port set of each side has size ≤k since it lies at distance exactly two from an opposite universal port. Its set of high nonports has size ≤k−3: from any opposite high nonport they are all at distance four, and the second layer of that opposite vertex separates it from them and has at least κ=3 members. Adding the anchors and the possible low nonport gives n≤4k−2.

Suppose universal ports occur on at most one side, and write t for their number. We have t≤k−1: if t>0, take any opposite port x. All t universal ports have distance two from x. Some anchor also has distance two from x, since its distances on the connected S include one and a value greater than one. For t=0 the bound follows from k≥1.

Sum the three positive-even budgets at the anchors. If S induces a three-vertex path, each end anchor spends one slot on the opposite end, leaving at most 3k−2 exterior vertices covered. If S is a triangle, each side contains some vertex even from at least two anchors. Indeed if that side has a port with just one incident anchor, the other two anchors are at exact distance two. Otherwise every port has two or three incident anchors; take a high nonport in the side and a port on a two-edge path from it to S. This nonport is at distance two from both or all three of that port's anchors. One such repeated incidence on each side again leaves at most 3k−2 distinct covered exterior vertices. Now

    n ≤ 3 + (3k−2) + t + 1 ≤ 4k+1.

If all nonports are high, the same proof gives n≤4k in the single-universal-side alternative.

## A disconnected separator joined by one ordinary vertex

Suppose now G[S] is disconnected. If some x outside S makes T=S∪{x} connected and no other universal port is adjacent to x, then again n≤4k+1. In particular this applies when G[S] has exactly one edge, an anchor on this edge is at distance two from the isolated anchor, and there are no universal ports. It also applies if a connector x can be chosen on the side opposite all universal ports, or if the universal ports form an independent set and x is universal.

Use the four closed even sets rooted at T, each of size at most k+1. Any missed vertex is at one common odd distance from the four roots, since T is connected. A high nonport has distance two to S and cannot be missed. A missed port sees every root at distance one and thus is a universal port adjacent to x, excluded by hypothesis. At most the single low nonport remains.

The union of the four closed even sets saves at least four slots at the roots themselves. Indeed G[T] is a claw if S is independent; if S has one edge it is a four-vertex path or a triangle with one pendant vertex. Each contains two distinct pairs of nonadjacent vertices joined by a length-two path. Each unordered pair charges the two roots themselves once beyond their respective self-charges. This gives n≤4(k+1)−4+1=4k+1. More precisely the same calculation gives n≤4k+1+h when h universal ports are adjacent to x.
