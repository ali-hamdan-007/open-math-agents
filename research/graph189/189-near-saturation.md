# A near-saturation bound for degree-two vertices

Lean verifies the stronger bound |V| ≤ 3σ − 1 for diameter at most three, a vertex
of degree two, and σ ≥ 4 in `Graph189DegreeTwoFinalBound.order_le_three_sigma_sub_one`.
The weaker uniform bound
|V| ≤ 3σ for σ ≥ 3 is kernel-checked in
`Graph189DegreeTwoAdjacent.order_le_three_sigma`. We assume the original
even-distance hypothesis from [Written on the Wall II, Conjecture 189](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).
The order range excluded here lies beyond the small-order results of
[Easwar and Johari](https://arxiv.org/abs/2609.11719).

Let z have degree two with neighbors a and b. Let W and R be the vertices
at distance two and three from z, respectively. Write A and B for the
vertices of R at distance two from a and b, respectively. They cover R
because every vertex of R sees W, and every vertex of W sees a or b.
Only z can have degree below σ.

Assume |V| ≥ 3σ. Since |W| ≤ σ, we have |R| ≥ 2σ − 3 > σ for σ ≥ 4.
Neither a nor b sees all of W, since otherwise one of A or B would contain
all of R. If a and b are adjacent, each middle-layer vertex missed by a
is at distance two from a, and the same holds for b. If they are
nonadjacent, each counts the other at distance two. Also in the
nonadjacent case each anchor must miss exactly one middle-layer vertex:
its degree is at least σ, and it has at most one neighbor outside W,
namely z. Thus in either case |A|, |B| ≤ σ − 1. The missed middle-layer
sets are disjoint because every vertex of W sees an anchor.

If |R| = 2σ − 2, then A and B are disjoint and both have size σ − 1.
Each anchor misses exactly one middle-layer vertex, say a misses p
and b misses q. Every vertex of A sees only q in W, and every vertex of
B sees only p in W. Also |W| ≥ σ − 1, hence |W| ≥ 3. Choose a shared
middle-layer vertex c in W ∖ {p,q}. It sees both anchors and has no neighbor
in R. It cannot see both p and q, for it would count all R and z at
distance two. It cannot see exactly one, for it would count the σ − 1
remote vertices through that one, the other missed middle-layer vertex,
and z. Thus c has degree at most 2 + (|W| − 3) < σ, a contradiction.

Therefore |R| = 2σ − 3, |W| = σ, and |V| = 3σ. The total number of middle-layer
misses by a and b is either two or three. If there are three misses, the
anchors are adjacent, and we can label the missed middle-layer sets
so that a misses p and b misses q₁,q₂. Then A and B partition R, with
|A| = σ − 1 and |B| = σ − 2, and B sees only p in W while A sees only
q₁ or q₂. A shared middle-layer vertex c exists because σ ≥ 4. It has
no neighbor in R, so it must see all but at most one of the other W
vertices. If it sees both q₁ and q₂, its distance-two count includes z,
all of A, and either p (if c misses p) or all of B (if c sees p).
Thus c sees p and exactly one of q₁,q₂, say q₁. Now c already counts z,
q₂, and all of B at distance two, so q₁ cannot see any of A. The vertex
q₁ therefore has no remote neighbors and must see every other W vertex
to have degree at least σ. In particular it sees p and q₂. Its own
distance-two count includes z via a, b via p, all of B via p, and all of A
via q₂, a contradiction.

If there are two misses, let a miss p and b miss q, and let
S = W ∖ {p,q}, of size σ − 2. If A and B are disjoint, one has size σ − 1
and the other size σ − 2. Relabel so that A is larger. Every c in S has no
neighbor in R and can miss at most one of the other W vertices. It cannot
see q, since then it counts all σ − 1 vertices of A, z, and either p or all
of B at distance two. Therefore c sees p and misses q. Every vertex of B
has only p as a neighbor in W, so its degree forces it to see a vertex of
A. Consequently q counts every vertex of B, every vertex of S, and z at
distance two. The count is 2σ − 3 > σ.

Finally, if A and B intersect, they each have size σ − 1 and intersect
in exactly one vertex. Each exclusive remote set has size σ − 2. Every
vertex of A ∖ B has only q as a neighbor in W, so to have degree at least σ
it needs a neighbor in B ∖ A. Its potential remote neighbors in its own
exclusive set and the common remote vertex total only σ − 2. Thus every
vertex of A ∖ B is at distance two from p, and symmetrically every vertex
of B ∖ A is at distance two from q. Hence p counts z and σ − 2 opposite
remotes at distance two, leaving room for at most one other vertex.
Every member of S that p misses would add one, because it shares an
anchor with p. Since |S| ≥ 2, p sees at least one member of S, which also
puts the opposite anchor a at distance two from p. Therefore p cannot
miss any of S. The same is true of q. But a member of S adjacent to both
p and q counts z and both exclusive remote sets at distance two,
giving 2σ − 3 > σ. This last contradiction proves the bound.

Lean separately checks the three geometric contradictions in
`Graph189DegreeTwoNearSaturation.lean`, as well as the numerical split
`near_partition_counts`. `Graph189DegreeTwoFinalBound.lean` derives every layer hypothesis of those
lemmas from the original graph, including both possible adjacencies between
the two neighbors of z. The audit lists only the standard Lean axioms.
