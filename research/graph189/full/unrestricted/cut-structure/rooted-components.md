# Rooted paths on both sides of a cut in large Graph 189 instances

Let G be connected with second-smallest degree k, order n ≥ 2k+3, and at most k vertices at positive even distance from each vertex. Let c be a cut vertex. By the checked component theorem, G−c has exactly two connected components, with vertex sets A,B. All edges from each component to the rest of G end at c. Let e(A) be the number of vertices in A at even distance from c, and similarly for B. The checked side inequality gives

    |A|+e(B) ≤ 2k,     |B|+e(A) ≤ 2k,     |A|,|B| ≥ k.

All vertices have degree at least two. Connectedness and the order assumption exclude a vertex of degree zero. If z has degree one with neighbor w, then {z} is a side at w. The same checked bound gives two or more vertices in every side.

We construct a spanning path of A∪{c} beginning at c. The argument applies to either component.

**If |A|≤2k−1**, add one marker r to G[A∪{c}], adjacent only to c, to obtain J. Each vertex of A retains its entire G-degree in J. Let H consist of the vertices in A with degree at least k. At most one vertex of A is outside H. For any two vertices of H, their degree sum is at least 2k ≥ |J|−1. Bondy–Chvátal path closure permits addition of their edge without changing traceability. Repeat until H is a clique. The marker retains degree one in the completed graph.

If H=A, start at r,c, continue to any contact of c in A, then take all remaining vertices of the clique. A contact exists by connectedness. Otherwise write u for the unique low vertex in A. When c is adjacent to u, start at r,c,u, go to a high neighbor of u, and take the remaining clique. Such a neighbor exists since u has at least two neighbors, all in A∪{c}. When c misses u, choose any contact x of c in A, which is necessarily high. Both of u’s first two neighbors are high, so choose one y distinct from x. From r,c,x traverse the clique ending at y and append u. This proves traceability after closure. Reversing the closure gives a spanning path in J. Its vertex r must be an endpoint, immediately followed by c after orienting appropriately. Deleting r yields the required rooted path.

**If |A|=2k**, then e(B)=0. Thus every vertex of B touches c. Otherwise a path in B to a contact of c would contain a vertex at distance exactly two from c. For each contact x∈A of c, every member of B lies at distance two from x, via c. Since |B|≥k, we have |B|=k and no vertex of A is at distance two from x. Connectedness of G[A] now forces x adjacent to every other vertex of A. In fact along any A-path from x to a nonneighbor, the first nonneighbor would have distance exactly two. Let P be the contacts in A and let Q=A∖P. The nonempty P is therefore a clique complete to Q. All of Q lies at distance two from c. Hence |Q|≤k and, since |A|=2k, |Q|≤|P|. Starting at c, alternately use a fresh contact then a noncontact. To absorb surplus contacts, place them at the beginning before the first alternating pair, or after the last noncontact. Each required edge is present. This gives a spanning path with first vertex c. The opposite side B can use the smaller-side proof (or observe directly that B is a clique, since every high vertex has exactly k candidate neighbors in B∪{c} and at most one vertex of B is low).

Construct the rooted path in each side. Reverse one rooted path and concatenate at c. The result visits every vertex of G exactly once. This establishes R2.H1 on paper. The proof only requires the checked two-component result. Uniqueness of the cut vertex is a stronger structural conclusion that can be proved separately. The path-closure step is the standard traceability criterion for an added edge with endpoint degree sum at least the order minus one.

## Lean verification

At the pinned Formal Conjectures and Mathlib revisions, Lean 4.33.1 accepted the full theorem `Graph189CutH1.cut_vertex_case` using the upstream `SimpleGraph.distEven` and `SimpleGraph.secondSmallestDegree`. Its hypotheses and conclusion are the R2.H1 proposition in upstream PR 11081. The warning-as-error compile exited successfully. The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The complete dependency list and SHA-256 hashes are in `h1-modules.sha256`, and the terminal output is in `h1.log`.

The principal proof steps are `Graph189CutCore.components_after_cut_eq_two`, `Graph189CutExtreme.rooted_at_two_k`, `Graph189SmallRoot.marked_trace_at_small_root`, `Graph189SmallRoot.rooted_of_marked_traceable`, and `Graph189CutJoin.hamiltonian_of_rooted_sides`. The independent `Graph189UniqueInterface.unique_cut_with_two_components` theorem establishes uniqueness of the cut vertex in this regime.

[Upstream reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11081) · [Easwar and Johari, Theorem 5.11](https://arxiv.org/abs/2609.11719)
