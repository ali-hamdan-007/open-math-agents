# The second-smallest degree three case

Suppose the second-smallest degree, counting repetitions, is three. The registered even-distance condition implies that each vertex has at most three vertices at distance two. Write δ for minimum degree and n for order. The previously checked order bound in `../../factor/Graph189OrderBound.lean` gives

    n ≤ 1 + δ + 3 + (3+1)²/4 = δ+8.

The checked cut-vertex and small-order theorems handle a cut vertex and n≤8. Hence consider a graph that stays connected after deletion of any single vertex, with 2≤δ≤3 and n≤11. When δ=2, n≤10. The argument below gives a short proof at these exact orders, using no circumference theorem.

Fix a longest path P. An attachment position of an omitted vertex u is an index i for which P[i] is adjacent to u. Positions are numbered starting at zero. All attachment positions of u are internal, and two of them cannot be consecutive. Otherwise extending or inserting u would make a longer path. The immediate predecessor and successor of each attachment are both at distance two from u. For t≥1 attachments these shifts give at least t+1 distinct vertices (the t predecessors and the successor of the last mark). Consequently an isolated vertex of the graph off P has degree at most two, since all its neighbors lie on P. Whenever an omitted vertex has two distinct attachments they differ by exactly two indices. A difference of at least three gives four distinct shifts.

If an omitted edge uv has a high endpoint v (degree at least three) then u retains at least half its degree off P. This is the genuine graph theorem `half_degree_outside_longest` in `../sep/cover/final82/lean/Graph189ExteriorDegree.lean`, with k=3. All distance-two counts are taken in the original graph.

**Components of order at least three.** Let C be such an omitted component. Every vertex u∈C that is attached to P starts a three-vertex path inside C. Indeed, if no such path exists, each neighbor of u in C is an interior-degree-one leaf. Since C is connected, these neighbors and u exhaust C. There are at least two leaves. If u is low, its two neighbors in C exhaust its degree and it cannot attach to P. If u is high, its leaves have ambient degree at most two by the exterior degree inequality. There is room for at most one low vertex.

An attachment at position i of any vertex of C must therefore have at least three P-vertices on each side of it. Otherwise replace the shorter tail by the three-vertex path. The path has at most n−3≤8 vertices. Consequently all attachments of C fit into at most two consecutive positions. They cannot occupy both, since a path in connected C between the corresponding exterior endpoints can be inserted between the two P vertices. They cannot occupy at most one either: the graph is connected, and deleting its sole attached P vertex would separate C from the other vertices of P.

**Two-vertex components.** Both endpoints of an omitted edge cannot be high when it forms its own component, by the same exterior degree inequality. Let a be the high endpoint and b the low. A high endpoint exists because only one vertex may be low. The vertex a needs at least two contacts on P and b needs one. The two shifts observation gives exactly two contacts of a, at positions i and i+2. All marks for this component have at least two P vertices on either side, since either endpoint can start a two-vertex exterior path. Here δ=2, n≤10 and |P|≤8, so these marks fit into at most four consecutive positions. For any contact j of b and either contact t of a, either j=t or |j−t|≥3. Otherwise replace the gap between the two contacts by the edge ab. No j in four consecutive positions meets this test for both i and i+2. Indeed j cannot equal either since the other is two away. If j is strictly between them its distance from each is one, and if j lies outside then its distance from the farther one would have to be at least five. This eliminates all two-vertex components.

**A single omitted vertex.** If P fails to span, all its omitted vertices are now isolated. Every isolated omitted vertex is low, so precisely one low vertex z is omitted. It has degree two and its contacts occur two positions apart. Replacing their midpoint on P by z produces another longest path, this time omitting only the midpoint. The midpoint is high and isolated off the new path, a contradiction.

The pinned Lean theorem `Graph189ThreeOriginal.traceable_three` proves the registered Hamiltonian-path conclusion assuming precisely the original connectedness and maximum-even bound, together with k=3. Its two-connected branches are `Graph189ThreeRegularMinimum.traceable_tied_three` at δ=3 and `Graph189ThreeLowMinimum.traceable_ten` at δ=2. The latter uses the independently checked midpoint exchange and the two-mark shift theorem. The original small-order and cut-vertex proofs discharge all other cases. The kernel reports only `propext`, `Classical.choice` and `Quot.sound` for the original-hypothesis theorem. The full conjecture at greater k is a separate obligation.

## Replaying the graph modules

Use Lean 4.33.1 and the formal-conjectures checkout at `9097e2f90e66` with its pinned Mathlib. From this document's directory the focused parent is regenerated from the registered binder as follows, with `OMA_FC` pointing to that checkout and `build` to a scratch directory.

```sh
python3 ../parent/make-focused.py ../parent/Graph189ParentAssembly.lean \
  "$OMA_FC/FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean" \
  "$build/Graph189ParentFocused.lean"
```

Copy the Lean sources below into the scratch directory using the module names as basenames. Compile in the listed order with the scratch directory prepended to the pinned project's `LEAN_PATH` and `lean -j1 -o "$module.olean" "$module.lean"`. The last source prints the axiom audit for the original-hypothesis theorem.

| Source directory relative to this document | Modules in compilation order |
| --- | --- |
| `../../factor/` | `Graph189ThirdLayer` |
| `./` | `Graph189R1Metric` |
| `../../factor/` | `Graph189OrderBound` |
| `../sep/cover/final82/lean/upstream/` | `Graph189TraceClosurePublic` |
| `../sep/cover/final82/lean/` | `Graph189ExteriorGap`, `Graph189ContactIntervals`, `Graph189ExteriorSpacing`, `Graph189ContactColumns` |
| `../lowblock/` | `Graph189SingleExteriorShift` |
| `../sep/cover/final82/lean/` | `Graph189ExteriorDegree`, `Graph189MatchedOrder` |
| `../order/` | `Graph189RootedPath` |
| `./` | `Graph189ThreeRegularMinimum`, `Graph189UniqueOmissionExchange`, `Graph189TwoMarkShift`, `Graph189ThreeSmallExterior`, `Graph189ThreeLowMinimum` |
| Scratch directory | `Graph189ParentFocused` |
| `./` | `Graph189ThreeOriginal` |
