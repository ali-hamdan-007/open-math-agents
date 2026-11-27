# Diameter four in Conjecture 189

Write σ for the second-smallest degree, Nᵢ(x) for the vertices at distance
i from x, and Tᵢ(x,y) for Nᵢ(x) ∩ Nᵢ(y). Assume a connected graph of
diameter at most four satisfying DeLaViña's even-distance condition.
[Written on the Wall II, Conjecture 189](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)

## Checked layer bounds

`Graph189DiameterFour.even_layers_four` gives
distEven(x) = 1 + |N₂(x)| + |N₄(x)|.
For vertices x,y at distance four, only the third and fourth layers
from x can contain neighbors of y. The fourth layer contains y itself,
so the checked `opposite_predecessor_lower` gives

$$
\deg(y)+|N_2(x)|+1\le \sigma+|N(y)\cap N_3(x)|.
$$

Across any edge xy, distances from a third vertex differ by at most one.
Distances have the same parity exactly when they are equal. Odd ties
contribute to neither even-distance count, whereas even ties contribute
to both. The checked `edge_tie_budget` therefore gives

$$
|V|+|T_2(x,y)|+|T_4(x,y)|
\le 2(\sigma+1)+|T_1(x,y)|+|T_3(x,y)|.
$$

In particular, at orders above 2σ + 3, every edge needs at least two more
odd ties than even ties. This refines the order-only bound on any graph
with a controlled edge-tie profile.

Under vertex-deleted preconnectedness, `Graph189CliqueLayers.endpoint_budget`
gives |N₂(x)| ≥ 2, σ ≥ 3, and deg(y) + 3 ≤ σ + |N(y) ∩ N₃(x)|.
These three conclusions do not require the layers to be cliques.

## Checked unbounded subfamily

`Graph189CliqueLayers.hamiltonian` assumes vertex-deleted preconnectedness
and that all distance layers from one diameter endpoint are cliques.
If an intermediate layer has already been entered at v, a path from the
diameter endpoint to the opposite endpoint avoiding v still crosses to
the next layer. Thus an exit at a distinct vertex is available. A path
inside each clique with the specified entry and exit yields a single
spanning path in layer order.

For unbounded examples within the actual Conjecture 189 hypothesis, take
five clique layers of sizes 1, k, k−1, k, 1 for k ≥ 3, with complete links
between consecutive layers. The graph remains connected upon deletion of
any one vertex. Both diameter endpoints have degree k, while every
other vertex has degree at least k. The largest even-distance count is
k+1, and the order 3k+1 exceeds 2k+3. This family lies outside the published
small-order and non-2-connected cases. [Easwar and Johari, arXiv:2609.11719](https://arxiv.org/abs/2609.11719)

## Diameter endpoint of degree two when σ = 3

The following is a paper argument. The higher-degree, non-clique case
of diameter four remains open.

Suppose z is a degree-two diameter endpoint with anchors a,b and σ = 3.
The checked endpoint budget forces |W|=2 and |F|=1, where W=N₂(z)
and F=N₄(z). Write R=N₃(z) and F={f}. Every vertex other than z has
degree at least three. Each remote has a neighbor in W. If either anchor
sees all W, every remote is at distance two from it, so |R|≤3 and the order
is at most nine. If the anchors are nonadjacent, each needs both W vertices
to have degree at least three. Thus the only case not covered by the known
small-order results has adjacent anchors, a sees only p in W, and b sees
only q. The other middle vertex already uses one distance-two slot at each
anchor, so each of p and q sees at most two remotes. Since the order is at
least ten, the remotes split into disjoint pairs Rₚ={u,v} and R_q={s,t}, and
the order is ten.

The vertex f has at least three neighbors, all in R, and so meets each
pair. Each of p and q has z, the opposite anchor, and f at distance two.
Thus p and q cannot be adjacent, since each remote of R_q would then be
another distance-two vertex from p. No cross edge joins Rₚ and R_q, since
it too would give an extra distance-two vertex from p. Every remote now
has only three possible neighbors, namely its corresponding middle
vertex, its pairmate, and f. The degree bound forces all these edges.
A Hamiltonian path is b–z–a–p–u–v–f–s–t–q.
