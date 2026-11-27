# Exact residual at k=6

Assume the bounded-order degree-three residual, with k=6. The attachment-group
argument eliminates every exterior order except the equality case

    n=20, |H|=4, |Q|=16, g=3.

Here H is K4. Equality in the group count has the following consequences.

1. There are exactly three attachment positions U on Q. Every group consists
   of its single representative, every outer tail used in the count has four
   vertices, every same-side inter-group interval has four internal vertices,
   and the intervals from the innermost positions to z have no spare vertex.
2. Every vertex of H is adjacent to every member of U. Indeed its three
   internal H-neighbors do not reach ambient degree six without all three
   positions. Therefore H has no other neighbor outside H, and H union U is
   the same seven-vertex block as in the earlier singleton-group analysis:
   a K4 complete to three ports.
3. For any h in H, every neighbor of U outside H union U is at exact distance
   two from h. Consequently the external boundary of U has size at most six.
   The Q-edges at U already give six distinct boundary vertices if all three
   ports lie on one side of z. In that case these are all U-boundary edges.
   If the ports split two on one side and one on the other, equality makes the
   two innermost ports share z as their Q-neighbor. Q then supplies five
   distinct boundary vertices, so at most one further U-boundary vertex exists.

This equality case is impossible. At least one port is adjacent to z along Q,
so all four vertices of H lie in D2(z). Suppose a neighbor x of z is not one
of the three ports. Every neighbor of x is either z, one of the other two
neighbors of z, or a member of D2(z). The vertex x is adjacent to no member
of H, because all H-neighbors on Q are precisely the three ports. Consequently

    degree(x) <= 1 + 2 + (6 - 4) = 5,

contrary to the fact that every vertex other than z has degree at least k=6.
Thus the three neighbors of z are exactly the three ports.

The Q-edges at the ports now finish the contradiction. Besides z, they give
at least four distinct vertices outside H union U adjacent to a port: four in
the two-plus-one split, and five when all ports are on one side. All of these
vertices lie in D2(z), as do the four vertices of H. Hence z has at least
eight vertices at distance two, exceeding its cap six.

This eliminates the last equality not covered by the uniform group-count
inequality.
