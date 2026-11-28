# When the two smallest degrees are both four

Let the two smallest entries in the degree sequence be four. The registered even-distance cap gives at most four vertices at distance two from any vertex. The layer-cover bound gives at most 15 vertices. The registered short-order and cut-vertex results let us assume the graph stays connected after deleting any one vertex.

Take a longest path P and let E denote its omitted vertices. The single-vertex shift and exterior degree-sum theorem give every vertex of E at least two neighbors in E. Consequently, if E is nonempty, it contains at least three vertices.

## At most three omissions

Let W be any connected component of E. Its minimum internal degree is at least two. Two-connectivity gives two disjoint edges from W to distinct positions i and j on P. Write u and v for their endpoints in W and put i before j.

A path on t vertices starting at u can replace the prefix strictly before i. A path on t vertices starting at v can likewise replace the suffix strictly after j. A u-to-v path on d vertices can replace the open interval from i to j. Thus P has at least 2t+d+2 vertices whenever both rooted paths exist.

Each root in W starts a three-vertex path. Connectivity gives a u-to-v path on at least two vertices. It follows that P has at least ten vertices and E has at most five. In fact a graph on at most five vertices with minimum degree two joins any distinct u and v by a path on at least three vertices. Delete the edge uv if present. Choose a neighbor c of u distinct from v, and a neighbor d of v distinct from u. The closed neighborhoods of c and d have at least three vertices each, so intersect. The edges they use, including uc and vd, survive the deletion. This gives the desired u-to-v path. Applying 2t+d+2 with t=d=3 gives at most four omissions.

If there are four omissions, W must comprise all four. It contains at least three vertices, and a vertex in any other component would require two neighbors in its own component. A graph on four vertices with minimum degree two admits a spanning path starting at any prescribed vertex by the rooted local Ore theorem. Taking t=4 and d=3 now gives at least thirteen vertices on P, which together with four omissions exceeds the maximum order.

## A tight tail in the three-vertex case

If P omits three vertices, they form a triangle, and each omitted vertex has at least two path contacts. All three vertices share precisely two contacts. Indeed, if their contact union had size greater than two, the Hall sharpening would give a matching of all three exterior vertices into three distinct path positions. The two outer tails and two intervening gaps would each contain at least three vertices by detouring through the triangle. The graph would have at least 18 vertices. Since the union has at most two elements and each row has at least two, all three contact rows coincide.

Mark the two common positions i and j. The prefix before i, the interval between i and j, and the suffix after j each have at least three vertices. They have total size at most ten. At least one of the outer tails therefore has exactly three vertices.

Replace that tail by a spanning path of the omitted triangle. The resulting path is also longest and omits just the three old tail vertices, so the same classification applies. The old bounding mark remains on the new path and is adjacent to the nearest omitted tail vertex. Since their contact rows coincide, that mark is adjacent to every omitted tail vertex.

Now fix any of the three originally omitted vertices x. The three old tail vertices are nonneighbors of x at distance two through the bounding mark. The immediate predecessor and successor of the other mark are also nonneighbors of x at distance two. They are distinct from the entire old tail because the two marks have at least three intervening vertices. This gives five different vertices at distance two from x, contradicting the cap.

The Lean entry point is `Graph189FourTiedOriginal.traceable_tied_four`. Its hypotheses consist of the original connectedness and maximum-even bound and the two degree equalities. Its supporting modules are `Graph189FourTriangle`, `Graph189FourTerminalGap`, `Graph189FourTail`, `Graph189FourRoutes` and `Graph189FourExterior`.
