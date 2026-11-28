# The four-port case at k=6 is impossible above order 20

**Theorem.** Suppose the unique low vertex z has degree five, the second-smallest degree and positive even-distance cap are six, and the disconnected configuration has (a,s)=(4,4). Then n≤20.

For n>20 there are five anchors A, two vertices of K complete to A, four ports P, and h=n−12≥9 third-layer vertices R. Each vertex of R meets at least one port. The component D=P∪R is connected. The following finite verification has no solver dependency. The C++17 source is k6-four-port-census.cpp, SHA-256 5d285b91b42311fbbcf775acf206db97e8464077dea4e560f1ecc55c7ddd7714. Compile with any standard C++17 compiler and run with no arguments.

## Shell enumeration

Represent the port neighbors of each anchor by a subset of four ports. Its subset cannot be all four since the entire third layer would then lie at distance two from this anchor. Sort the five subsets, and keep the least sorted tuple under all 24 port permutations. Each port needs an anchor. There are 546 remaining tuples. Try all 1024 graphs on the five anchors and all 64 graphs on the four ports, including all labelings of each sorted tuple.

Write S_p for a port's neighbors in R. For any anchor a with incident port set I(a), impose

    |⋃_{p∈I(a)} S_p| ≤ min(5, 6 − missed anchors − missed ports reached in two shell edges).

Every counted member lies at distance two from a. The independent bound of five follows from an extra witness: a missed anchor via z, or, if complete to the other anchors, a missed port via an adjacent anchor. Any anchor touching all ports was excluded. The shell degree of a is three plus its number of anchor and port neighbors; require this to be at least six. For each p use the intersecting anchor-union bounds to cap |S_p| (call this cap s_p) and require |S_p|≥6−d_A(p)−d_P(p).

Each port p already sees K and z at distance two. Let b_p be three minus the number of nonneighbor anchors and other ports reachable in two edges inside A∪P. A negative b_p rejects that shell. There can be at most b_p third-layer vertices at distance two from p. In particular the union of all supports of ordinary port neighbors of p, together with S_p, has size at most s_p+b_p.

Propagate all union bounds to subsets by monotonicity, then to disjoint unions by addition. This bounds h. A private vertex, one with just port p, needs a neighbor in R−S_p since |S_p|≤5. Thus it lies at distance two from some other port. There are at most Σb_p private vertices, and a private vertex on p requires s_p+b_p≥6. If x is the total private count, incidence counting gives 2h−x≤Σs_p. These inequalities bound h by each of

    (Σs_p+Σb_p)/2,
    (Σs_p+Σ_{p:s_p+b_p≥6} s_p)/2.

After all these bounds, exactly 38 shell records have upper bound 9 and 26 have upper bound 10. None has a larger bound.

## Remote types

For each retained shell and permissible h, choose the four-port neighbor subset M_x of each of the h core vertices. These nonempty subsets are listed in sorted order to remove duplicate permutations, and every union-size and individual support bound is checked. Recompute the distance-two port pairs now known from overlaps S_p∩S_q. Subtract newly witnessed port pairs from b_p. An x outside S_p also consumes a slot at p whenever an ordinary neighbor of p lies in M_x. Reject infeasible mandatory counts and private totals.

Next choose Z_x to be the set of ports at distance two from x. It is disjoint from M_x, contains every mandatory port just described, and is nonempty for a private x. Counts at each p are bounded by its remaining b_p. Sort the Z_x within each equal M_x class. It suffices to allow all pairs satisfying these tests, even though extra constraints could exclude some of them.

Two core vertices x,y can be adjacent only if

    M_x ⊆ M_y∪Z_y   and   M_y ⊆ M_x∪Z_x.

Indeed each port of x missing y would be at distance two from y via x. The graph of all such possible edges overestimates the available degree. Reject a type assignment if an x has fewer than six neighbors even after counting all possible core neighbors and its actual port mask.

| h | Shell + core mask assignments | After assigning distance-two port sets | After core degree check |
|---|---:|---:|---:|
| 9 | 36 | 266 | 0 |
| 10 | 4 | 4 | 4 |

All four final outputs have the same D. The ordinary port graph consists of two independent edges pq and rs. Five core vertices have mask {p,q}, the other five have mask {r,s}, and every Z_x is empty. There are no possible cross-edges between the two five-sets. The entire D is therefore disconnected, a contradiction. The four outputs differ only in G[A]. This is an exhaustive exclusion of h≥9.

With the k=6 component, two-port, and three-port manuscripts, every k=6 degree-five case with disconnected G−N[z] is now covered.
