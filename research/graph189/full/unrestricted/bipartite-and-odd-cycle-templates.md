# Large-order blow-ups of bipartite bases and odd cycles

Each template vertex v is replaced by a nonempty module of size w_v inducing either a clique or an independent set. Template edges expand to complete joins. Distances between different modules coincide with template distances: a template shortest path lifts to the blow-up, and a blow-up path projects to a template walk after collapsing consecutive visits to a module. In a clique module the other vertices are at distance one; in an independent module they are at distance two because the template is connected and has at least two vertices. Throughout, k denotes the second-smallest graph degree and the positive even-distance cap is k.

## Bipartite bases

**Theorem.** A qualifying blow-up of a connected bipartite base with at least two vertices has a spanning path whenever its order n exceeds 3k+2.

Let A and B be the two nonempty base parts. Write W_A,W_B for their total weights and m_A,m_B for their minimum weights. For any module v in A its positive-even count is at least W_A−w_v, since all other modules of A have positive even distance. If the module is independent the count equals W_A−1.

If there is an independent module in A, then W_A≤k+1, so W_B>2k+1 by the order hypothesis. A minimum-weight module of B satisfies W_B−m_B≤k, hence m_B>k+1. Therefore B has only one module, since another module of weight at least m_B would itself exceed its cap. That sole module is a clique because an independent module would force W_B≤k+1. The base is a star, so the clique is complete to all vertices on the A side. It is large enough to place a distinct clique vertex between each successive pair of arbitrary A vertices and to append any remaining clique vertices, giving a spanning path. This also treats an independent module in B by exchanging the parts.

Hence all modules may be assumed to be cliques. The minimum-weight modules give W_A≤k+m_A and W_B≤k+m_B, so
\[
 m_A+m_B\ge k+3.
\]
If both parts had at least three modules, each minimum module would see at least twice its own weight at positive even distance, giving 2m_A≤k and 2m_B≤k, impossible.

If one part is a singleton, let p be the center clique weight and b the number of peripheral cliques. When b=1 the graph is a clique. Otherwise, if a smallest peripheral clique has size r and degree ≥k, the cap there is at least (b−1)r and its degree is p+r−1, so (b−2)r≤p−1. If that smallest clique has degree below k, it must be the unique low-degree singleton. Take r to be the second-smallest peripheral size. The cap at the singleton is at least (b−1)r, and the degree of a size-r peripheral vertex is p+r−1≥k, giving the same inequality. Thus b≤p+1. List the peripheral cliques in any order, joining each consecutive pair through one center vertex and allocating surplus center vertices to any such run. This is a spanning path.

In the remaining case let |A|=2 and b=|B|≥2. We have m_A,m_B≤k from the even cap on their respective smallest modules. Thus both are at least three. If b=2 then all weights exceed the corresponding base degrees. If b≥3, the even cap gives (b−1)m_B≤k. Consequently m_A≥k+3−m_B≥k/2+3, while b≤k/3+1 since m_B≥3. Again every module weight is at least its base degree: A weights are at least b and B weights are at least three whereas their base degrees are at most two. Any connected clique blow-up with these capacities is traceable. Double a template spanning tree, single the edges along a chosen nontrivial tree path, and take an open Euler trail. Each base vertex has at most its base degree many visits. Expand each visit into a nonempty run in its module to use all clique vertices. This completes the proof for a bipartite base.

## Odd-cycle bases

**Theorem.** A qualifying blow-up of a cycle of odd length l≥5 has a Hamilton cycle when n>3k+2.

Each module has two neighboring modules, so all graph degrees are at least two. If k=2, every module sees the two second-neighbor modules at distance two; their total weight is at least two and at most k, forcing all weights to equal one. This case is the original cycle.

If every module is independent, write W=Σ_v w_v. The sum of the positive even-distance counts over one representative per module is at least 3W−l, from its own twins and two second-neighbor modules. The sum of these degrees is 2W, and at least l−1 module representatives have degree at least k; the remaining degree is at least two. Thus
\[
 3W/l-1\le k\le (2W-2)/(l-1).
\]
This gives (l−3)W≤l(l−3), hence every weight is one. Again the conclusion follows.

We can therefore assume k≥3 and at least one module is a clique. Use the strict neighborhood expansion theorem: a 2-connected graph of order above 2k+2, with all but at most one vertex of degree at least k and at most k distance-two vertices from every vertex, has |N(S)|≥|S|+1 for every nonempty independent set S. This is the theorem proved in strict-expansion.md. The hypotheses apply here: deleting one vertex either leaves all cycle modules occupied or leaves a path of nonempty modules; both yield a connected graph. All other hypotheses follow from the metric and order assumptions.

For each base vertex i set \(a_i=w_i-1\), and let I be the base vertices of independent modules. For every base-independent subset \(T\subseteq I\), we have
\[
 a(T)\le a(N_H(T)),
\]
where a(X) is the sum over a set X. To see this, consider the incidence graph of the edges between T and its base neighborhood. Each vertex of T has degree two in this incidence graph and every vertex on the other side has degree one or two. Its components are paths: a cycle component would have to be the entire base odd cycle, but the incidence graph is bipartite. Each path therefore has one more neighborhood vertex than T vertex. For each path separately, the vertices of G in its T modules form an independent set. Their neighborhood consists exactly of the modules of the other side of that path. Strict expansion says the sum of the weights on the neighborhood side is at least one above that for its T side. Subtracting the module counts gives the displayed a-inequality for the path, and summing gives it for T.

There exist nonnegative real edge amounts x_e with incident sums a_i for i∈I and sums at most a_i for other vertices. To prove this, maximize the sum of the incident amounts over I with all incident sums constrained above by a_i. The linear-program dual minimizes \(\sum_i a_i y_i\) over y_i≥0 with \(y_i+y_j\ge \mathbf 1_I(i)+\mathbf 1_I(j)\) on each edge. Set \(z_i=y_i-\mathbf 1_I(i)\). The negative level set \(T_t=\{i:z_i\le-t\}\) is independent and contained in I for any t>0. Its neighbors all have \(z\ge t\). The displayed inequality implies \(a(\{z\ge t\})\ge a(T_t)\). Integrating in t gives \(\sum_i a_i z_i\ge0\). Therefore every dual objective is at least \(a(I)\), and the primal optimum, bounded above by \(a(I)\), attains it by linear-program duality. All demands at I are saturated.

The amounts can be made integral. Take an extreme point of the feasible set with the demands fixed. If the nonintegral edges formed a path component, its two endpoints would each have incident sum nonintegral: the other incident edge, if present, is integral. Thus neither bound at these endpoints can be tight, and alternating sufficiently small positive and negative perturbations along the path preserve all internal sums and both endpoint bounds. This contradicts extremality. So if any edge is nonintegral, all edges of the cycle are nonintegral. Every incident sum must then be tight as well, because if one sum had slack, alternating perturbations around the odd cycle would preserve all other sums and change only the slack sum. Each tight sum is integral, so the fractional parts of consecutive edges add to one. Odd cycle length forces all fractional parts to be one half. Round alternately up and down around the cycle, taking the two edges incident with a chosen clique module both down. This preserves every other incident sum and decreases the chosen clique's by one, so all constraints still hold and all amounts are nonnegative integers.

Now give every base edge multiplicity \(1+2x_e\). The resulting connected multigraph is Eulerian. In its cyclic Euler tour, the module at i occurs \(1+\sum_{e\ni i}x_e\) times. This is exactly w_i on independent modules and at most w_i on clique modules. Assign every independent twin to its own visit and expand the clique visits into nonempty runs using all clique vertices. Consecutive runs join along base edges, including the closing join. The result is a Hamilton cycle.

The odd-cycle proof only uses strict independent-set expansion in the mixed case (when some module is independent and some is a clique).
