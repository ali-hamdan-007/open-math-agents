# Nonadjacent anchors with one miss each

Let the degree-two vertex be z, with nonadjacent neighbors a and b.
Let W and R be the vertices at distance two and three from z, with
|W| = 5 and |R| = 6. Every vertex except z has degree at least 5,
and every vertex has at most 5 vertices at distance exactly two.
Suppose a and b each miss one vertex of W. Every vertex of W sees
at least one anchor, so the missed vertices are distinct. Let x be
missed by a, let y be missed by b, and put C = W minus {x,y}.

Write X for the vertices of R whose W-neighborhood is exactly {x},
and Y for those whose W-neighborhood is exactly {y}. Each vertex of
R has a W-neighbor and no neighbor among z, a, and b. Because a sees
all of W except x, every vertex of R outside X is at distance two
from a. The vertex b is also at distance two from a via z. Thus
6 − |X| + 1 ≤ 5, giving |X| ≥ 2. Likewise |Y| ≥ 2.

Every vertex r of Y has only y as a neighbor outside R. Its degree
inside R is at least 4, so it misses at most one other vertex of R.
As X and Y are disjoint and |X| ≥ 2, r is adjacent to some vertex
of X. Therefore all of Y is at distance two from x: each r has a
two-edge path to x through X and no direct edge to x. In addition,
z and each vertex of C nonadjacent to x is at distance two from x
via b. If x had no neighbor in C, this would give at least six
vertices at distance two from x. Therefore x has a neighbor in C,
and a is at distance two from x through that neighbor. By symmetry,
y has a neighbor in C and b is at distance two from y.

The distance-two count at a now includes b, x, and R outside X.
Thus |X| ≥ 3, and symmetry gives |Y| ≥ 3. Since X and Y are disjoint
subsets of R, they are both of size three and partition R. The
distance-two count at x includes the three vertices of Y together
with z and a. It follows that x is adjacent to every vertex of C,
since any nonneighbor in C would add a sixth vertex via b.
Likewise y is adjacent to every vertex of C.

Choose any c in C. It has no neighbor in R because X and Y partition
R. But it is connected to each vertex of X by a two-edge path through
x, and to each vertex of Y through y. Thus all six vertices of R
are at distance two from c, a contradiction.
