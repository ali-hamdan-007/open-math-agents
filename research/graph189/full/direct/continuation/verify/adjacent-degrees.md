# Traceability when the degree set is contained in {k,k+1}

Let G be finite, simple and connected, let k be its second-smallest degree, and suppose every vertex has degree k or k+1 and at most k other vertices at positive even distance. Then G has a Hamilton path, for every order and every k. This statement includes regular graphs as well as the two-degree case with minimum k. The key order-restricted part below only assumes that every vertex has degree at least k.

When n>4k+1 the local inequality in wedge-order-and-hamiltonicity.md gives the L0 condition at every induced two-edge path. The local Ore theorem therefore gives a Hamilton cycle. Assume henceforth n≤4k+1. The verified small-parameter results dispose of k≤5. Cut vertices are covered by the known cut-vertex theorem. If κ=2, the separating-pair theorems for components consisting wholly of high vertices apply. These cover at least three components, two deep components, and each shallow case for adjacent or nonadjacent anchors. The last missing shallow nonadjacent case is in ../sep/shallow-high-two-cut.md, together with the earlier deep-high-two-cut.md, shallow-adjacent.md and shallow-private-two-cut.md from the globalcut checkpoint.

It remains to prove the following order-restricted claim. If k≥6, κ≥3, every vertex is high and n≤4k+1, the graph is traceable. Suppose not. Let P be a longest path and pick an omitted component C. The earlier exterior theorems give internal degree at least h=ceil(k/2) to each vertex of C and |C|≥h+2.

## A cycle of length at least k−1 outside P

First assume C is 2-connected, of size m. If m≥k−1, Dirac's circumference theorem gives the desired cycle. If m≤k−2, then C is Hamilton-connected by 2δ(C)≥m+1. Each member has at least a=k−m+1 contacts on P, and there are at least a members in C. A cover of fewer than a vertices of the bipartite contact graph would leave an uncovered C vertex with a surviving contact. Thus a distinct contacts on each side can be matched by König's theorem. Each of the a−1 intermark gaps and both tails has at least m unmarked vertices by longestness, since the entire component can be traversed between the matched contacts or from a single such contact on a tail. Therefore

    n ≥ m(k−m+3)+k−m+1.

This concave quadratic attains its minimum on h+2≤m≤k−2 at an endpoint. Its value at k−2 is 5k−7, which exceeds 4k+1 for k≥9. At the lower endpoint it equals t²+4t+1 for k=2t and t²+5t+2 for k=2t+1. These exceed 4k+1 for even k≥10 and odd k≥9, respectively. For k=6,7 the interval is empty. This leaves only k=8, m=6, and equality n=33.

In this equality case P has 27 vertices. Every C–P edge can be included in a matching of size three: after fixing it every other C vertex has at least two contacts remaining, so match two more distinct vertices. All four intervals from any three matched marks contain at least six unmarked vertices. Equality forces their marks to have indices 7,14,21 in the path indexed from 1. Thus these are all possible marks, and each C vertex is adjacent to all three. The same fixed contact vertices must occupy those positions in every longest realization on the same vertex set, including every path obtained by rotations.

Let e be the initial endpoint of such a path. If e has a neighbor at position j>7, rotate by reversing the first j−1 vertices and keeping the suffix from j onward. The former mark at position 7 is now at position j−7, necessarily a multiple of seven. Thus e's only possible neighbors are positions 2 through 6 and the three marks. To obtain a high endpoint avoiding the marks, fix an orientation and the far endpoint. The eight or more neighbors of the starting endpoint yield distinct new endpoints by these rotations (including the trivial reversal of a one-vertex prefix), none equal to the fixed far endpoint. The two endpoints of a longest nonspanning path cannot be adjacent, because closing it into a cycle would allow extending from an exterior vertex. Together with the fixed endpoint there are at least nine attainable endpoints. None has a neighbor outside P. Those adjacent to a mark all lie at distance two from any fixed x∈C, so there are at most eight of them. Some attained endpoint therefore avoids all marks and has degree at most five, contradicting its high degree. This excludes the equality case.

If C has a cut vertex, choose a leaf block B with cut w and b vertices. Every noncut vertex has degree at least h in B, so b≥h+1 and this is not a bridge. If b≥k−1, Fan's circumference extension of Dirac gives the desired cycle: every distance-two pair in B includes a vertex of internal degree ≥h. Suppose b≤k−2. The graph B−w has minimum degree ≥h−1 and is Hamilton-connected since 2(h−1)≥b. Each of its b−1 members has at least a=k−b+1 path contacts; b−1≥a. Match a distinct such vertices to distinct marks on P. The intervening gaps have at least b−1 vertices each. Each tail can do better. From its matched port traverse all of B−w ending at a neighbor of w other than the port, which exists by two-connectivity of B. Append w and a rooted path through at least h vertices of R=C−B: start at a neighbor of w in R, since in its R-component all vertices lost at most w from their C-neighborhoods and have degree at least h−1. Thus each tail adds h+1 more vertices than b−1. Also |R|≥h. Counting as above,

    n ≥ b(k−b+3)−1+3h+2.

At b=k−2 this exceeds 4k+1 because k+3h>10. At b=h+1 the difference from 4k+1 equals t²−2t+2 for k=2t and t²−t+3 for k=2t+1. Both are positive. Concavity excludes the entire interval, including k=6,7,8. This proves the cycle claim.

## Three distinct cycle contacts

Take a cycle D of length d≥k−1 outside P. Since κ≥3 there are three disjoint D–P paths with distinct endpoints. Trim them to avoid both sets internally. Each tail at the three marks on P can traverse the full cycle, and each of the two interior gaps can traverse its longer D arc, containing at least ceil(d/2)+1 vertices. Counting D, the marks, gaps and tails gives

    n ≥ 3d+3+2(ceil(d/2)+1).

At d=k−1 this exceeds 4k+1 for even k, and equals 4k+1 for odd k. Equality leaves precisely D outside P, since the displayed bound already counts all vertices. The exterior C then contains a spanning cycle, has order k−1, and has minimum degree at least h, so C is Hamilton-connected. Use the same two connectors bounding either gap and traverse all d vertices of C instead of only ceil(d/2)+1. Since k≥6, this strictly increases the lower bound, a contradiction. This completes the theorem.
