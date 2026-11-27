# A counting lemma for adjacent anchors with one private vertex each

Let z have degree two, with adjacent neighbors a and b. Suppose all
vertices are within distance three of z. Write W and R for the vertices
at distances two and three. Assume a and b each miss exactly one vertex
of W, and that at least one vertex of W is adjacent to both a and b.
Write p for the vertex seen only by a and q for the vertex seen only by b.

Suppose every vertex other than z has degree at least s, and the number
of vertices at distance exactly two from any vertex is at most s. If
s ≥ 5, then |R| ≤ 2s − 4. In particular the order-14 shape with s = 5
and |W| = 4 is impossible since |R| = 7.

Let Eₐ be the vertices of R sharing a neighbor with a, and define Eᵦ
similarly. Each vertex of R has a neighbor in W, so Eₐ ∪ Eᵦ = R. The
vertex q is at distance two from a via b and is outside R. Thus
|Eₐ| ≤ s − 1, and similarly |Eᵦ| ≤ s − 1.

Set A = R ∖ Eᵦ and B = R ∖ Eₐ. The sets are disjoint and each has
size at least |R| − s + 1. A vertex of A has p as its only neighbor in W,
and a vertex of B has q as its only neighbor in W. Hence every vertex
of A or B has at least s − 1 neighbors in R. A vertex of B must have a
neighbor in A, since the complement of A in R is Eᵦ and contains at
most s − 2 candidates other than the vertex itself. Each vertex of B
is therefore at distance exactly two from p through a vertex of A.
Symmetrically, all vertices of A have distance two from q.

Suppose |R| ≥ 2s − 3. Then each of A and B has size at least s − 2.
The vertices z and b are at distance two from p via a. Together with B,
they fill p's distance-two cap. Every c in W adjacent to both anchors
must therefore be adjacent to p, because otherwise a witnesses that c
is an additional vertex at distance two from p. The same argument at q
forces qc. But c has no neighbors in A ∪ B, by their purity, and c
reaches all of A ∪ B at distance two via p or q. This gives at least
2s − 4 > s vertices at distance two from c, a contradiction.
