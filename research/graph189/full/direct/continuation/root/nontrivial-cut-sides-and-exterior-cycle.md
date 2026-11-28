# Every minimum-cut side is nontrivial, and long cycles survive outside a longest path

Let a counterexample have order n, connectivity s and second-smallest degree k. We have s≥5 and 3s<k by the earlier results. Then its minimum degree exceeds s. Consequently every component of a minimum cut contains a high vertex (one of degree at least k), and the small high population X on either nonempty side of a minimum cut is at least k−s. In particular the following order upper is unconditional:

    n ≤ 2k+1+floor(sk²/(k−s)).

To prove the first assertion, only a unique low vertex z with degree exactly s needs treatment. If z lies in any minimum cut S, minimality forces z to have a neighbor in each of two distinct components A and B. Choose such neighbors a,b, both high. Their component-internal closed neighborhoods have at least k−s+1 members each. Those disjoint sets are all at distance one or two from z; at most k are at distance two. Thus z has degree at least 2(k−s+1)−k=k−2s+2>s, impossible. If z belongs to no minimum cut, universal-minimum-order.md gives n≥(s+2)(k−s+1)−1. Apply the local root layer cover bound at z with all s neighbors. The function t(k+1−t) increases up to s as 2s<k. This gives n≤1+s+k+s(k+1−s), smaller by exactly k−3s>0. This exhausts the possibilities.

A singleton after deleting a minimum s-cut would have degree at most s. Since at most one vertex is below k, every nonempty union of components now has a high vertex. Its ≥k−s internal neighbors and itself include ≥k−s high vertices. Let X≤Y count the high vertices of a partition into two nonempty groups. The cut-product inequality gives XY≤kX+sk². In particular X²≤kX+sk² and hence X≤sk for s≥2 (the quadratic at sk is nonnegative). Set a=k−s. Then a≤X≤sk²/a so (X−a)(X−sk²/a)≤0. Rearranging and using the product bound gives X+Y≤a+k+sk²/a. At most s+1 further vertices remain, proving the displayed upper bound.

For a second structural conclusion, take any minimum-degree vertex z, let H=G−z, and take ANY longest path P in H. There exists a cycle outside P in H of length ≥ceil(k/2) by universal-minimum-order.md. More is forced. Take any positive integer L≤ceil(k/2) satisfying

    (L+1)(k−L+2) ≥ n+2.

Then H−P contains a cycle of length at least k−L+2. To see this, complete z to a universal vertex in G, forming K with minimum degree at least k. Closing P through z gives a longest cycle of K (one avoiding z could insert z). Apply Nikoghosyan's Theorem 2: the exterior circumference is either at most L−1 or at least δ(K)−L+2, under the displayed order condition. Its former alternative is impossible by the cycle of length ≥ceil(k/2). The whole cycle obtained lies in unchanged H−P, so is a cycle of G.

The unconditional order upper gives an explicit choice of L from k and s. In particular, along sequences s tending to infinity the independently known s≤(1+o(1))sqrt(k) yields n≤(s+3+o(1))k. Now L=s+4 satisfies the inequality for all sufficiently large s: (s+5)(k−s−2)≥(s+4−o(1))k. Thus deleting any minimum-degree vertex and any longest path in the remainder still leaves a genuine cycle with at least k−s−2 vertices. This proves a necessary condition on any counterexample. The extremal path P is in H, and the conclusion makes no assertion that this outside cycle can already be spliced into P.

Source: Zh. G. Nikoghosyan, On Some Versions of Conjectures of Bondy and Jung, Theorem 2, https://noad.sci.am/Content/136032/03%20%281%29.pdf.
