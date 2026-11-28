# Cut vertices in large Graph 189 instances

Let G be a finite connected graph, k its second-smallest degree, and n its order. Assume n ≥ 2k+3 and that each vertex has at most k+1 vertices at even distance, counting itself. Deleting a cut vertex leaves exactly two connected components.

The main theorem is `Graph189CutCore.components_after_cut_eq_two`. Its file defines the even-distance count and degree order statistic using the literal expressions from the pinned Formal Conjectures source. `Graph189CutInterface.components_after_cut_eq_two` gives the same theorem in terms of `SimpleGraph.distEven` and `SimpleGraph.secondSmallestDegree`, which are the declarations used by the upstream R2.H1 statement.

## Proof

Take a nonempty side S attached to a single gate c. Each edge leaving S ends at c. Connectedness gives a contact x in S adjacent to c. For every y outside S, every walk from x to y goes through c. Thus d(x,y) equals 1+d(c,y), so y belongs to one of the even-distance sets at c and x. These sets also cover x and every vertex of S at even distance from c. Consequently

    |V∖S| + |{y∈S : d(c,y) is even}| + 1 ≤ 2k+2.

The order assumption yields |S|≥2. At most one vertex lies below degree k, and each vertex of S has at most |S| neighbors. Hence |S|≥k.

Suppose three disjoint sides S,T,U have the same gate. The sets T,U and the gate already contribute at least 2k+1 to the first term in the displayed inequality for S. The second term vanishes. If S contained a nonneighbor of c, a path from that vertex to c would give an element of S at distance two from c. Every vertex of S thus touches c, and the same holds for T and U. A contact in S then sees every vertex of T∪U at distance two. Their number exceeds its budget. Applying this to components after deletion gives the upper bound of two. Disconnectedness after deleting a cut vertex gives the matching lower bound.

This formalizes the obstruction to three components sharing a single cut vertex directly from Graph 189's assumptions. Theorem 5.8 of Easwar and Johari proves a stronger statement about the entire block tree on paper. The supplied handwritten argument in `unique-cut.md` deduces uniqueness of the cut vertex without requiring a block-tree development. The remaining rooted path result in their proof of the complete cut-vertex case is Lemma 5.10.

[Upstream reduction 11081](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11081) · [Easwar and Johari, sections 5.8–5.11](https://arxiv.org/abs/2609.11719)

## Verification

Lean 4.33.1, Formal Conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Run Lean in a checkout at these pins, with the current directory and the checkout's dependencies on its search path.

```sh
lean -DwarningAsError=true -o Graph189CutCore.olean Graph189CutCore.lean
lean -DwarningAsError=true -o Graph189CutInterface.olean Graph189CutInterface.lean
```

The core file has passed warning-free kernel checking. Its axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`.
