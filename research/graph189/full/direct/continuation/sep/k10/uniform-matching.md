# Exterior contact matchings with arbitrary connectivity

Work in a hypothetical nontraceable Graph 189 graph with second-smallest degree k, h=ceil(k/2), and 3≤s=κ≤floor(k/2). The above-half cases have been separately solved. Fix a longest path P and a high-bearing exterior component C subject to the known exterior hypotheses, including high internal degree ≥h and order m≥h+2. The inequalities below use no maximum-degree assumption. They isolate a minimum cut and a nearly complete small component in the full line s=floor(k/2)−1.

## Bounds for general s

If C has a cut vertex, choose an endblock B with all noncut vertices high. Let b=|B|≥h+1 and q be their least degree inside B, so q≥h. Its complement in C contains a high vertex, since otherwise the lone low vertex has only the articulation as a C-neighbor, and the earlier path-contact inequality gives ambient degree at most two. Thus |C−B|≥h.

- At b≥2q−1 choose a Fan cycle of length ≥2q−1. There exist s disjoint connectors from it to P. The two exterior tails on P each contain ≥2q−1 unmarked vertices, and each of the s−1 inner gaps contains ≥q+1 by the longer cycle arc. Counting C as well gives
```
n ≥ (s+5)q+2s+h−4.
```
- At b≤2q−2, B minus the articulation is Hamilton-connected. Its bipartite contact matching to P has size at least j=max(s−1,k−b+1). A cover of fewer than s−1 together with the articulation would separate the remaining interior from P. The k−b+1 bound follows because every noncut has so many contacts and at least that many noncuts exist. Between two matched interior points one can traverse all b−1 noncuts. Each outer tail instead traverses the entire block to its articulation and at least h−1 following vertices in C−B, by the high-degree remainder argument (potentially one low there). Hence
```
n ≥ (j+2)b+3h−1
  ≥ 3h−1+min((h+1)(k−h+2),(s+1)(k−s+2)).
```
The last bound follows by concavity of b(k−b+3) up to the transition b=k−s+2 and monotonicity thereafter.

If C is 2-connected, let q be the least internal degree among its high vertices. At m≥2q the analogous Fan cycle of length 2q gives
```
n ≥ (s+5)q+2s−1.
```
At m≤2q−1, C has a spanning cycle. Any pair of distinct terminals has a spanning path except possibly the two C-neighbors of a low vertex of C-degree two. For that single exceptional pair there is a path with m−1 vertices. These facts follow by adding a degree-two terminal marker and applying ordinary cycle closure to the high vertices. Any j matched contacts therefore give
```
n ≥ (j+2)m+j−1,
```
improved by one if no exceptional pair intervenes. Here j≥s by the separator bound on bipartite vertex covers.

In particular, if n<(s+3)m+s and C is in this last case, its contact matching has size exactly s. A minimum cover has p marks of P and s−p vertices of C. Since at least one high C vertex avoids the cover, its ≥k−m+1 contacts require p≥k−m+1. Removing this cover separates C minus its covered vertices from the remaining P. Every uncovered high C vertex is a genuine port of this minimum s-cut when m≤k; the low one is too when δ>m−1. If m=k−s+1, the cover contains only marks, C is a clique and all its high members touch every mark. More generally at m=k−s+2 either all cover vertices are marks, or precisely one lies in C. In the latter alternative C minus that vertex is a clique whose high members touch all the new cut vertices: all need the s−1 covered marks and all m−1 neighbors within C to achieve their degree. It is thus connected.

In the full-mark clique case every piece between and beyond the s marks on P has at least m unmarked vertices. An attainable high endpoint e that avoids all marks exists by the k+2 endpoint-set result and the quota on a high C member. For its orientation of P, let σ be the sum of the s+1 piece sizes above m. Its at most m−1+σ permitted neighbors give σ≥k−m+1=s: a neighbor in the first m positions of a piece after a mark would rotate e to a path with initial tail shorter than m. Thus
```
n ≥ (s+2)m+2s.
```

## One below half connectivity

Write t=floor(k/2) and s=t−1≥3. Assume k≥9 in the odd case and k≥10 in the even case. Put U=t²+5t+1 for k=2t, respectively U=t²+6t+4 for k=2t+1; the proven order bound is n≤U−(k−δ).

All three large-component alternatives above exceed U. At even k, the bounds for the large endblock, smaller endblock and large 2-connected component are respectively at least t²+7t−6, t²+6t−1 and t²+6t−3. They exceed U for t≥5. At odd k, the three are at least t²+8t−1, t²+7t+2 and t²+7t+1 (the first follows with h=t+1); all exceed U for t≥4. In the remaining 2-connected near-Hamilton-connected case, a matching of s+1=t would cost at least (t+2)(h+2)+t−1, which is U+2 at even k and U+1 at odd k. Thus its largest matching has size exactly s, and the preceding structural cut applies.

At even k we obtain m≥k−s+1=t+2. At m≥t+3, the s-matching lower bound is already U. Equality would have no low vertex by the degree-sensitive order bound, removing the one-vertex exceptional allowance and increasing that lower bound. Therefore m=t+2. This is a clique complete to the s marks on every high member, with n≥(s+2)(t+2)+2s=U−1. At U there is no low member; at U−1 its deficit is at most one. In particular a low clique vertex could miss only one mark. Actual neighbors of the s marks on P provide 2s distinct exterior ports, while the quota of a high clique member gives at most k=2s+2 such ports in the whole outside. This is a parameter-uniform necessary configuration, not an assertion of its feasibility. The fixed s=4 case is excluded in traceability-k10.md.

At odd k we obtain m≥t+3 and m≤t+4 by the s-matching bound. At m=t+3 the full-mark clique configuration has n≥U−3. At m=t+4 one has n≥U−2, and the cover has at least s−1 marks. With one covered member u in C, C−u is the clique described above (Hall multiplicity two is established for actual path marks, not for u). With all s vertices on P, each high member touches at least s−1 marks and has at least m−2 internal neighbors; a miss of one mark entails full internal adjacency. This gives a precise remaining alternative at arbitrary t.

## Sharpness of the local deductions

The one-vertex allowance in terminal routing is indispensable for the degree-only block lemma. A clique augmented with a vertex z adjacent only to two vertices u,v has no spanning u,v-path once another clique member exists; removing z gives such a path of order m−1. This is a local example, not a Graph 189 counterexample. The elementary contact-cover conclusion also cannot force a marks-only cover as soon as each exterior vertex needs one fewer mark than the matching size. Take at least s+2 left vertices adjacent to the same s−1 marks, and give exactly one left vertex two further private marks. The maximum matching size is s and the unique size-s cover uses that left vertex and the original s−1 marks. Finally, a mixed cover does not justify two path-neighbors at a covered exterior vertex: only actual marks on an oriented path have predecessor and successor vertices there.

The graph inputs and proofs being parameterized are the exterior-degree and size bounds, terminal-pair closure, matched-gap/tail estimates and endpoint rotations in ../../global/max-degree-plus-two-exception.md, ../../global/three-consecutive-degrees-all.md, and ../../lowblock/high-connectivity-complete.md. The quadratic inequality is the independently kernel-checked Graph189OrderBound.order_le theorem recorded there. Fan's circumference theorem, Menger's theorem, König's theorem and the Bondy–Chvátal closure theorem are used in their ordinary graph-theoretic forms.
