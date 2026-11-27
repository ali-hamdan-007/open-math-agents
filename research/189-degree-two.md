# Degree-two cases of Written on the Wall II, Conjecture 189

The conjecture asks for a Hamiltonian path under the bound on even-distance
sets from [DeLaViña’s catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).
Write δ for minimum degree and σ for second-smallest degree.

## Checked traceability when δ = σ = 2

`Graph189LowDegreeTwo.traceable_min_two_sigma_two` proves the diameter-at-most-three
case with at least six vertices. The result also falls within the small-order
and connectivity results of [Easwar and Johari, arXiv:2609.11719](https://arxiv.org/abs/2609.11719).
The Lean proof is direct and needs neither an independent-set neighborhood
hypothesis nor a finite search.

Take a degree-two vertex z. Its distance-two layer W has at most two elements.
Suppose the distance-three layer R has at least three. A vertex w of W has
at least two neighbors in R, since each vertex of R has a neighbor in W.
Choose a neighbor a of z adjacent to w. The two remote neighbors of w fill
the distance-two layer of a. The other neighbor b of z must be adjacent to
a, or b would also be at distance two from a. Every vertex of W is adjacent
to a or b. If one were adjacent to b alone, it would add another distance-two
vertex of a. Therefore a sees all of W. Every vertex of R is then at distance
two from a, contradicting the cap. This proves |R| ≤ 2, hence |V| ≤ 7.

The remaining layer sizes (|W|, |R|) are (1, 2), (2, 1), and (2, 2). The proof
constructs paths for these three shapes. In the last shape, the two vertices
of R may share just one neighbor w in W. If they are adjacent to each other
and the other vertex v of W misses w, both neighbors of v are among a and b.
The path then runs z–b–v–a–w through the two vertices of R, with a chosen
to be adjacent to w.

## Checked larger-order structure

`Graph189DegreeTwoOuter.large_nonadjacent_layout` treats diameter at most three,
σ ≥ 3, order at least 2σ + 4, and a degree-two vertex z with nonadjacent
neighbors a and b. This is outside the small-order interval of Easwar and
Johari's theorem. The distance-two layer W has exactly σ vertices and the
distance-three layer R has at least σ + 1. The vertices a and b have degree
exactly σ. Each misses exactly one vertex of W, with distinct missed vertices
p and q, respectively.

The distance-two count at a already includes b, so at least two vertices of
R are at distance three from a. Every such vertex has p as its unique neighbor
in W. The same holds with b and q. Lean certifies the exact layer sizes, the neighborhood restrictions, and
the lower bound of two on both remote classes. The corollary
`Graph189DegreeTwoOuter.remote_unique_middle` proves the unique middle-layer
neighbor assertion.

The result rules out order ten when σ = 3 and a and b are nonadjacent.
In this case W has three vertices and R has four. The two remote classes
have two vertices each and partition R. The third middle-layer vertex c
can have no neighbor in R. An edge from c to p or q would exceed one of
the distance-two counts at a or b. This leaves c with degree at most two,
contradicting its degree lower bound. Lean checks this as
`Graph189DegreeTwoOuter.not_order_ten_of_nonadjacent`. For both neighbor configurations, the checked theorem
`Graph189DegreeTwoAdjacent.order_le_three_sigma` bounds the order by 3σ when
σ ≥ 3. In particular σ = 3 forces order at most nine, across both placements
of the neighbors. This excludes every σ = 3 degree-two case beyond the
small-order results of Easwar and Johari. See the [near-saturation proof](189-near-saturation.md)
for a further improvement at σ ≥ 4 and its verification status.

The optional script `search_189_layers.py` makes seeded, layer-constrained
random draws for σ = 3 through 9, looking only at orders from 2σ + 4 through
3σ + 3. It found no graphs passing all tested conditions. These trials were
exploratory and are independent of the proofs.
