# A sharp third-layer inequality and an unrestricted Graph 189 order bound

Let G be a finite simple graph and fix a vertex z. Write L_j for the vertices at distance j from z. If each anchor a∈L₁ has at most k vertices at distance two, there is a t≤min{|L₁|,|L₂|,k+1} such that

    |L₃| ≤ t(k+1−t) ≤ floor((k+1)²/4).

Take a smallest subset T of L₁ whose neighborhoods cover L₂. If L₂ is empty the assertion is immediate. For each a∈T choose a private b_a∈L₂ adjacent to a but to no other member of T. Such b_a exist by minimality and are pairwise distinct. Every vertex of L₃ is at distance two from some a∈T, by taking a predecessor in L₂ and then a covering anchor. Let t=|T|. For a fixed a and each j∈T∖{a}, there is an extra distance-two witness: use b_j if a and j are adjacent, and otherwise use j itself via z. These t−1 witnesses are distinct and in L₁∪L₂. Thus a sees at most k+1−t third-layer vertices at distance two. Sum over T and apply the square inequality. The proof needs no connectivity assumption when distance layers are defined on the component of z. The local-distance inequality is sharp: put t arms z–a_i–b_i on a common root and give each b_i exactly k+1−t pendant leaves for a maximizing t. Each vertex has at most k vertices at distance two and the third layer has t(k+1−t) members.

Now let G satisfy Graph 189. Write k for the second-smallest degree, δ for the minimum and select z of degree δ. The upstream R1 lemmas give diameter at most five, and every pair at distance five contains a vertex below degree k. All vertices other than z have degree at least k. For every a∈L₁ and f∈L₅ we therefore have d(a,f)=4: distance is between four and five and these endpoints are both high. All |L₅| points consume distinct additional even-distance places at each selected anchor. Since |L₂|+|L₄|≤k at z, we obtain

    n ≤ 1+δ+k+ max_{0≤t≤δ} t(k+1−t) ≤ 1+δ+k+floor((k+1)²/4).

When L₃ is nonempty, T is nonempty and the stronger intermediate estimate is |L₃|+|L₅|≤t(k+1−t)−(t−1)|L₅|. If L₃ is empty then L₅ is empty as well. The previous R1 upper bound was (δ+1)(k+1). For δ≤(k+1)/2 the new upper bound is at most 1+δ+k+δ(k+1−δ), improving the old bound by δ(δ−1). For δ≥(k+1)/2 the quadratic term, independent of δ, gives the stronger value. For k=3 and δ≥3 this gives n≤11 without a case split. External reference for the underlying conjecture and prior traceability criteria: https://arxiv.org/abs/2609.11719.

## Formal verification

`Graph189ThirdLayer.lean` constructs a minimum anchor cover and its private second-layer vertices and proves `third_layer_product` and `third_layer_quadratic` with actual finite graph distance and only a local exact-two cap. It also proves `order_quadratic` from the root's and anchors' even-layer budgets. `Graph189OrderBound.lean` derives these budgets and the resulting uniform quadratic order bound directly from the exact original maximum-even-distance cap and connectivity. The upper bound optimized over t before taking the square is stated on paper; the Lean file separately proves existence of t and the unconditional quadratic bound.

`Graph189R1Metric.lean` compiles the exact upstream R1 source from its first variable declaration through its `diameter_le_five` proof, using the genuine graph-degree and vertex-distance module imports. This is a focused dependency, not a redefinition of graph invariants. `third-layer-lean.log` and `order-lean.log` show the three standard axioms for all four new theorems in Lean 4.33.1 with warnings-as-errors. `check-third.sh` records the local replay. No claim of full traceability or upstream verdict is made.
