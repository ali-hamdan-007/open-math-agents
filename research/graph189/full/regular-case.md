# The regular case of Conjecture 189

Let G be a finite, simple, connected, k-regular graph, k≥2. Suppose that each vertex has at most k other vertices at positive even distance. Then G has a Hamilton cycle.

For a regular graph the second-smallest degree is k, so this proves the regular case of the conjectured Hamilton-path statement, in every diameter. A connected graph of degree one is K₂ and has the required path. The case k=2 is a cycle. Throughout the proof below take k≥3. Write Nᵢ(v) for the vertices at distance i. The hypothesis gives |N₂(v)|≤k. Whenever |N₂(v)|=k, no vertex is at distance four from v. A shortest path to any more distant vertex would pass through distance four, so v then has eccentricity at most three.

## The local theorem supplying the decomposition

Asratian's local Hamiltonicity theorem says that if a connected k-regular graph satisfies |N₂(v)|≤k and every induced ball of radius two is 2-connected, then the graph has a Hamilton cycle. Moreover, if a vertex z is a cut vertex of any radius-two ball, the induced ball B₂(z) minus z has exactly two components X,Y, of order k each, and every neighbor of z sees all the other vertices of its component. These are Theorem 1.6 and Lemma 2.2 respectively in A. S. Asratian and J. B. Granholm, “On Hamiltonicity of regular graphs with bounded second neighborhoods,” Discrete Applied Mathematics 316 (2022), 75–86. [Published paper](https://doi.org/10.1016/j.dam.2022.02.018) · [Preprint with theorem numbering](https://arxiv.org/pdf/2107.07037)

The first result handles the case of 2-connected balls. Otherwise a radius-two ball is connected, has more than two vertices and has a cut vertex z. Apply the second result. Set

- A=N(z)∩X, B=N(z)∩Y, a=|A|, b=|B|;
- P=X∖A, Q=Y∖B, T=N₃(z).

Both A and B are nonempty, a+b=k, |P|=b and |Q|=a. Each vertex of A has exactly z and the other k−1 members of X as its neighbors. The analogous statement holds for B. Since B₂(z) has order 2k+1, its second layer has order k, giving eccentricity(z)≤3. Thus z, X, Y, T exhaust the graph.

Every t∈T has a neighbor in P or Q. Define Tₚ={t∈T: t sees P} and Tq={t∈T: t sees Q}. A fixed vertex of A has all b vertices of B and all vertices of Tₚ at distance two. Thus |Tₚ|≤a, and symmetrically |Tq|≤b. Each p∈P has a neighbor in T because only the other k−1 members of X are available to it outside T. Each q∈Q likewise has a neighbor in T.

## A remote vertex meeting both sides

Suppose t∈Tₚ∩Tq. Every vertex of A∪B is then at distance two from t. These k vertices exhaust its distance-two allowance and imply eccentricity(t)≤3.

Let F be the subgraph induced by P∪Q∪T. Every component of F contains a vertex of T by the preceding degree argument. If F had another component besides that of t, take t'∈T in the other component. A path from t to t' must pass through a vertex of A∪B∪{z}. Each endpoint is at distance at least two from that complement of F, hence their distance is at least four. This contradicts eccentricity(t)≤3. Thus F is connected.

If a vertex of F were nonadjacent to t and distinct from it, the first two edges of a shortest F-path toward it would give a distance-two vertex of t in F, contrary to N₂(t)=A∪B. Hence t is adjacent to all other vertices of F. All its neighbors are in F, and |P∪Q|=k. Consequently |T|=1. Each p∈P must now see all k−1 other vertices of X and also t. The corresponding statement holds in Y, so X and Y are cliques. Choose a₀∈A,p₀∈P,q₀∈Q,b₀∈B. Traverse X as a spanning a₀–p₀ path, then t, then Y as a spanning q₀–b₀ path, and close through z.

## Remote vertices meeting one side each

Now T is the disjoint union U=Tₚ and V=Tq. Write u=|U|≤a and v=|V|≤b. Both sets are nonempty. There must be a cross edge r₀s₀ with r₀∈U, s₀∈V. Otherwise removing z separates X∪U from Y∪V. Fix r∈U and s∈V. Each vertex of A is at distance two from r through a neighbor in P. Each vertex of B is at distance four from r through z, and s is at distance six from r through z. This gives at least |A|+|B|+1=k+1 other vertices at positive even distance, a contradiction.

Fix any a₀∈A, b₀∈B. The left side L=G[X∪U] has the following degrees.

| Vertex | Degree in L | Reason |
|---|---:|---|
| p∈P | k | All its neighbors belong to X∪U. |
| x∈A | k−1 | Its sole neighbor outside X is z. |
| r∈U | at least k−v≥a≥u | Its external neighbors can belong only to V. |

To construct a spanning path with prescribed endpoints a₀,r₀, augment L by one vertex m adjacent only to a₀ and r₀. The augmented order is N=k+u+1. Bondy–Chvátal cycle closure preserves Hamiltonicity when a nonedge is added whose endpoint degrees sum to at least N.

1. Initially a₀,r₀ are nonadjacent and have degrees k and at least u+1. Add their edge.
2. The degree of a₀ is now at least k+1, so it joins all of U. The degree of r₀ is at least u+2, so it joins all of X, whose degrees are at least k−1.
3. Every vertex of U has gained a₀ and now has degree at least u+1. Every vertex of X has degree at least k, since all A vertices gained r₀ and all P vertices already had degree k. Complete the edges between X and U.
4. Each X vertex has degree at least k and each U vertex sees all k members of X. Since u≤a≤k−1, we have 2k≥N. Complete the pairs inside X and inside U.

The result consists of a clique on L together with m adjacent to the two prescribed endpoints, and has a Hamilton cycle. Consequently the augmented original graph has a Hamilton cycle. Removing its degree-two vertex m leaves the desired spanning a₀–r₀ path in L. Interchanging the sides gives a spanning s₀–b₀ path in G[Y∪V]. Join them with r₀s₀ and the two edges b₀z,za₀. This is a Hamilton cycle in G.

The proof also gives the diameter-three version using only |N₂(v)|≤k, since that hypothesis implies the full even-distance condition in diameter three. The paper directly proves Hamiltonicity for k=3,4,5 without a diameter bound under only the second-neighborhood hypothesis (Theorems 3.1, 3.2, 3.4). The step for general k above uses the full even-distance bound after the published cut-ball decomposition.
