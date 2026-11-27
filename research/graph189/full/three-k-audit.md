# Independent audit of the n ≤ 3k argument

The proof in `three-k.md` checks as a handwritten theorem, using the two stated local lemmas. Every distance-two witness below lies outside its source vertex's component of G−S, so its exhibited two-edge walk is a shortest path. The positive even-distance cap is k because the published convention counts the source vertex at distance zero.

## Published inputs

- Easwar–Johari, Theorem B(2)–(4), gives traceability when n≤2k+3 or G is not 2-connected. Its Lemma 3.1 gives path closure at degree sum at least the current order minus one. Both statements were checked in the original PDF. [Source](https://arxiv.org/pdf/2609.11719)
- Jianping Li's Theorems 8 and 9, p. 197, have the quoted weak inequality thresholds. The p. 196 definition prints “maximum” for the ambient degree sum of independent sets. This is a typographical error: the paper invokes Ore through σ₂, and the proof explicitly uses σ₃(X) as a lower bound on an arbitrary independent triple's degree sum (equation (12), p. 200, and the outline proof of Theorem 8, pp. 206–207). The minimum convention is also used explicitly by the same author in the 1997 joint paper. In this application every independent triple has ambient degree sum ≥3k≥n and ≥3α(X). Theorem 9 therefore applies directly. [Li](https://combinatorialpress.com/article/ars/Volume%20048/volume-48-paper-18.pdf)
- The abstract of Broersma, Li, Li, Tian and Veldman states the required prescribed-set criterion α(X)≤κ(X) for 2-connected G. With α(X)≤2 and noncomplete G[X], κ(X)≥2. In the complete case, |X|≥3. Opening an X-covering cycle at a neighbor of the only possible omitted vertex z gives the spanning path. [Source](https://doi.org/10.1016/S0012-365X(96)00071-4)

In the reduction, n≥2k+4 and n≤3k give k≥4. The preceding n≤δ+2k theorem applies when δ=k. Otherwise there is one low vertex z. For any independent (k+1)-set in X=V−{z}, a pair at distance ≥3 would yield two disjoint neighborhoods disjoint from that set, of total order ≥2k. This would give n≥3k+1. Otherwise the saturated-independent-set lemma applies. The two local lemmas in `split-ball/order-bound.md` and `split-ball/saturated-independent.md` have the needed hypotheses.

## Failing cuts

A 1-toughness violation has t≥s+1 and s≥2. One representative from each component is independent. Taking a high representative whenever possible gives s≤k, and s≤k−1 if every component contains a high vertex. Any component with a high vertex has order at least k−s+1, and a minimum-order high vertex is adjacent to all of S. Every high vertex in a component of order ≤k has an S-neighbor. A nonsingleton has at least two vertices adjacent to S, as one attachment vertex would be a cutvertex.

| Branch | Order/count checks |
| --- | --- |
| Every component high-bearing, 3≤s≤k−2 | The endpoint values of s+(s+1)(k−s+1) are 4k−5. Only k=5,s=3,n=15 remains. The three other size-three components contribute ≥6 witnesses. |
| Every component high-bearing, s=2 | Three components of size ≥k−1 with at most one excess vertex. One minimum-size component avoids z. The other two components each have order ≤k and contribute at least 2(k−1)−1 high attachment vertices collectively. |
| Every component high-bearing, s=k−1 | Exactly k components, each size ≥2 with at most one excess vertex. There is a minimum pair avoiding z. The other k−1 components contribute ≥2(k−1) witnesses. |
| Singleton z, 4≤s≤k−2 | The endpoints of 1+s+s(k−s+1) equal 4k−7. Only (k,s)=(6,4),(7,4),(7,5) survive the order bound. There are exactly s high components, with respectively ≤1, 0, 0 excess vertices. Some minimum component exists, all high components have order ≤k, and the other high components plus z contribute at least 10, 13, 13 witnesses, respectively. |
| Singleton z, s=3 | At least three high components of size ≥k−2 with at most two excess over the three required minima. A minimum component exists, each component has order ≤k, and the other high components plus z contribute ≥2(k−2)+1. |
| Singleton z, s=k−1 | At least k−1 high components of size ≥2 with at most two excess. A minimum pair exists for k≥4. There are ≥2(k−2)+1 witnesses. |
| Singleton z, s=k | There are k high components, and fewer than 2k high vertices outside S force a singleton x with N(x)=S. The other k components contribute ≥k witnesses, with an extra one for any nonsingleton. Thus all are singletons, giving n=2k+1, excluded. |

The row overlap for k=4,s=3 is harmless. In the final singleton-z, s=2 branch, three high components would force equality n=3k and all join completely to S, giving at least 2(k−1)+1 witnesses. With two high components A and B, each attaches to both cut vertices p,q by 2-connectivity. Also N(z)={p,q}.

For a component C of order c, work in C plus q and a new leaf r at q. The closure threshold is c+1, and every C vertex has degree ≥k−1 there. For c≤2k−3 this completes C. In a graph with C completed, start r,q and enter the clique at an original q-neighbor. Closure implies a spanning path in the unclosed graph, where the leaf is an endpoint and forces the edge r,q and then an original attachment into C.

The only larger component order is b=2k−2, forcing a=k−1. A vertex of A then sees all of S and witnesses z and every B attachment vertex at distance two. Thus at least k−1 vertices of B miss S and have augmented degree ≥k. With threshold 2k−1, complete every edge of B incident to this group. If the group has at least k vertices, each remaining B vertex now has degree ≥k. If the group has exactly k−1 vertices, a q-neighbor outside it has augmented degree ≥k and can be joined to every B vertex. Then each remaining B vertex has degree ≥k. In either case closure completes B and the original-q-neighbor conclusion follows. Use a p-neighbor endpoint for A and a q-neighbor endpoint for B, joining through p,z,q. The audit found no missing cut case or threshold gap.
