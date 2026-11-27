# The diameter-at-most-three degree-two case

**Theorem.** Every finite connected graph satisfying Conjecture 189's even-distance hypothesis, with minimum degree two and diameter at most three, has a Hamilton path. The construction below also proves traceability for any diameter when the minimum degree is two, the second-smallest degree k is at least five, and the order n is at most 3k−1.

## Traceability at the required order

Suppose k≥5 and n≤3k−1. Fix the degree-two vertex z with neighbors a,b. Since k>2, every vertex other than z has degree at least k. We may suppose G is 2-connected by Easwar–Johari's Theorem B. Set J=G−z; it is connected. A (k+1)-vertex independent set in J consists of vertices of degree at least k in G. Two of them at distance at least three would give two disjoint neighborhoods of size at least k outside the set, requiring 3k+1 vertices. Thus any such set meets the saturated-set criterion from saturated-independent.md. This gives a Hamilton path in G. Hence suppose α(J)≤k.

Only a,b can have degree below k in J, and they have degree at least k−1. Thus every independent triple of J has degree sum at least 3k−2, regardless of the edge ab. Write N=|J|≤3k−2.

First suppose J is 2-connected. It is in fact 1-tough. Otherwise a set S of s≥2 vertices would leave t≥s+1 components; the independence bound implies t≤k, hence s≤k−1. Each component has size at least k−s+1 unless it consists entirely of a,b, and each deficient component still has size at least k−s.

1. At s=2 a deficient component would contain at least k−2≥3 vertices all belonging to {a,b}, impossible. Hence N≥2+3(k−1)=3k−1, a contradiction.
2. For 3≤s≤k−2 there is at most one deficient component since each contains at least two anchors. It loses at most one vertex from its lower size bound. Consequently N≥s+(s+1)(k−s+1)−1. The expression is concave in s and equals 4k−6 at either endpoint, exceeding 3k−2 for k≥5.
3. At s=k−1 we have t=k and at most 2k−1 vertices outside S. At least one component is a singleton anchor x. It sees all k−1 vertices of S in J. If there is exactly one singleton, the other k−1 components all have size two, and at least k−2 of them contain no anchor. If there are two singleton anchors, at most one other component has size greater than two and there are at least k−3 ordinary two-vertex components. Thus in both cases at least two components are ordinary pairs. Both vertices of each ordinary pair must see all of S to reach degree k. From x, at least one vertex of every other component is at distance two via S, and each of the two ordinary pairs contributes a second vertex as well. These k+1 distinct vertices are also at distance two in G because all are original J vertices nonadjacent to x and the two-edge paths via S still exist. This violates the cap.

The 1-tough circumference bound of Bauer, Veldman, Morgana and Schmeichel (Theorem 9 of “Long cycles in graphs with large degree sums”) now gives circumference at least min{N, N+(3k−2)/3−α(J)}>N−1, since the triple sum is at least N. If α(J)<3, Chvátal–Erdős gives the same conclusion. Hence J has a spanning cycle. Start at z, enter the cycle at either a or b, and traverse the cycle with one edge removed there. [Bauer et al., primary paper](https://ris.utwente.nl/ws/files/6736746/Bauer90long.pdf)

Now suppose J has a cut vertex v. Any component C of J−v has |C|≥k−1, since a member of C can have outside neighbors only z and v in G. Equality would force every one of its k−1 vertices to see both z and v, impossible because z has only two neighbors and k≥5. Thus every component has at least k vertices. Since |J−v|≤3k−3, there are exactly two components, each of size at most 2k−3.

For either component C augment G[C∪{z,v}] by a marker vertex adjacent just to z,v. Each member of C retains all its original neighbors and has degree at least k. The augmented order is at most 2k, so ordinary Bondy–Chvátal cycle closure completes C. There are distinct vertices of C attaching to z and v: both z and v have a neighbor there by 2-connectivity of G, and if their whole attachment set consisted of a single vertex, removing that vertex would separate the other members of C from G. In the completed component a spanning path connects the chosen distinct attachments. This produces a Hamilton cycle in the augmented graph after closure, so the original augmentation also has a Hamilton cycle. Removing its degree-two marker gives a spanning z–v path through C. Combine the two such paths from the two components to get a Hamilton cycle in G.

## The verified order hypothesis

The existing theorem in parallel/fresh-wow/Graph189DegreeTwoFinalBound.lean:639 has the following literal signature.

```lean
theorem order_le_three_sigma_sub_one (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 4 ≤ G.secondSmallestDegree) (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree - 1
```

This covers both configurations of the two neighbors of z. It gives the preceding n≤3k−1 assumption for all k≥5. At k=4 it gives n≤11=2k+3, handled by Easwar–Johari. At k=3, parallel/fresh-wow/Graph189DegreeTwoAdjacent.lean:327 gives n≤3k=9=2k+3 under the same diameter and degree-two hypotheses. At k=2 the direct checked theorem Graph189LowDegreeTwo.traceable_min_two_sigma_two gives traceability when n>5; the remaining orders are covered by Easwar–Johari. The conclusion for arbitrary orders is restricted to diameter at most three by the available order theorem. No diameter restriction was used once n≤3k−1 was assumed.
