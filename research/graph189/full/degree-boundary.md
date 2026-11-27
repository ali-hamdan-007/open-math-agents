# The first order beyond Easwar–Johari’s bound

Let σ be the second-smallest degree and let n = 2σ + 4. Suppose G is
2-connected and satisfies Conjecture 189’s even-distance condition.
The argument applies to irregular graphs, including those with one
vertex of degree below σ. It uses the path closure rules in Lemmas 3.1
and 3.3 of [Easwar and Johari](https://arxiv.org/abs/2609.11719).
The thresholds at this order are 2σ+3 without a common-neighbor
condition, 2σ+2 with at most one common neighbor, and 2σ+1 with none.

## Raising the degree-(σ+1) vertices

Take a closure-saturated supergraph H. Suppose a vertex v has unchanged
degree σ+1. Its odd-distance set in G has size at least σ+3, so at least
two of its vertices are not neighbors of v. At most one can have degree
below σ, so choose a good odd-distance nonneighbor w. The original
neighborhoods of v and w are disjoint. In H, the neighborhood of v is
unchanged. When the degree of w in H is σ, σ+1, or at least σ+2,
respectively, the pair qualifies for the no-common-neighbor,
one-common-neighbor, or ordinary path closure rule. Each case is a
contradiction. All vertices of original degree at least σ+1 thus have
degree at least σ+2 in H.

This is proved in Lean by `Graph189BoundaryHigh.far_good` and
`Graph189BoundaryHigh.raise_middle`. The latter states saturation
under the published rules as explicit hypotheses.

## Few original vertices of degree at most σ

Let U be the vertices of original degree greater than σ and C the
vertices of original degree at least σ. The vertices in U form a clique
in H by the ordinary rule. At most one vertex is outside C.

If at most σ original vertices have degree at most σ, then U has at
least σ+4 vertices. Every vertex of U has degree at least σ+3 in H.
Any vertex in C can therefore join all of U. The resulting degrees
force C to be a clique, then force every vertex of C to join the
possible exceptional vertex. The closure is complete.

If exactly σ+1 original vertices have degree at most σ, then U has
σ+3 vertices. Any original degree-σ vertex gaining an edge in H can
join all of U. Each vertex of U then has degree at least σ+3, giving
complete closure as before. Otherwise all good vertices outside U
are unchanged. Connectivity gives an edge from U to its complement,
so some q in U has degree at least σ+3 and is adjacent in H to every
good vertex. Its edges to unchanged vertices already existed in G.
Hence pairs of nonadjacent good vertices outside U share q in G.

Take an unchanged good vertex x outside U. If y is an original
nonneighbor of x in U, it is also a nonneighbor in H. Saturation
implies that its H-degree is exactly σ+2 and that it has at least
two H-common neighbors with x. Since its original degree is at
least σ+1 and x is unchanged, at least one common neighbor existed
in G. Thus each good nonneighbor of x other than x is at distance
two in G. There are at least σ+2 of them, contradicting the bound.

Consequently the conjecture holds in this subfamily by the published
closure lemmas: they preserve traceability at every step, so a complete
closure implies a Hamiltonian path in the starting graph.
`Graph189BoundaryHigh.complete_of_few_low` proves the saturation
argument in Lean. The closure lemmas themselves are not formalized here.

The hypothesis is nonvacuous for unbounded, nonregular graphs with an
exceptional low vertex. For σ ≥ 4, take five clique layers of sizes
1, σ−1, 3, σ, 1, with complete links between consecutive layers.
The endpoint degrees are σ−1 and σ and the interior degrees exceed σ.
The graph is 2-connected, and each layer has at most σ vertices in the
other layers at even distance. Its order is 2σ+4.

## One more degree-count level

The next extension is a paper proof. Suppose exactly σ+2 original
vertices have degree at most σ, so |U|=σ+2. At least σ+1 good
vertices lie outside U. Call a good vertex outside U promoted if
its H-degree is at least σ+1.

If two good vertices are promoted, both join all of U, raising every
vertex in U to degree at least σ+3. This gives complete closure. If
exactly one is promoted, it joins all of U and has H-degree at least
σ+2. Its union with U is therefore a clique of size σ+3. Connectivity
supplies an edge from this clique to its complement, giving a vertex q
of H-degree at least σ+3. Every unchanged good vertex outside the clique
is originally adjacent to q. For any such x, its good nonneighbors in U
have original distance two by the preceding two-common-neighbor argument.
Its good nonneighbors outside the enlarged clique likewise have original
distance two via q. At most one good nonneighbor, the promoted vertex,
was omitted. Thus at least σ+1 vertices are at distance two from x,
contradicting the cap σ.

If none is promoted, each good low vertex has at least two original
neighbors in U: otherwise at least σ+1 nonneighbors in U would be at
distance two already. There are at least σ+1 good low vertices, so the
number of edges from U to them is at least 2σ+2. Since |U|=σ+2, some
q in U sees at least two such vertices. Its H-degree is then at least
σ+3, since U is a clique. Again q is a common original neighbor of
all unchanged good low vertices, leading to the previous contradiction.

Thus an unresolved boundary counterexample must have at least σ+3
original vertices of degree at most σ. This sharper degree-count
exclusion has not been integrated in Lean.
