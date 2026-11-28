# A small side at every large minimum separator

Let G be a hypothetical counterexample, let k be its second-smallest degree, and let S be a minimum vertex separator of size s. The preceding results allow s≤floor(k/2)−2. A high vertex has degree at least k. Partition the connected components of G−S into any two nonempty groups, and let X≤Y count the high vertices of the groups. Then

1. If s≥14, X<3k.
2. If s≥24, X<(2+8/s)k.
3. For s≥15 there is one component outside which fewer than 3k high vertices of G−S remain. For s≥24 the sharper number in (2) applies also to this assertion.

These estimates hold with the possible low vertex in the separator or in either group; connectivity within a group is unnecessary. In particular as s tends to infinity, the smaller side has at most (2+o(1))k vertices even if the graph order grows as s times k.

Use the global order bridge n>2k+s(k+1)/2 from ../lowblock/geodesic-width-and-order.md. Every crossed high pair has distance at most four. At positive even distance each source accounts for at most k targets. In an odd pair the distance is exactly three; a separator vertex on a shortest path is adjacent to one endpoint and at distance two from the other. At each anchor there are at most k neighbors in either group, since a contact from the opposite group sees all of them at distance two. Every minimum-cut anchor has a contact in each component. The counts of distance-two high vertices on both sides at one anchor sum to at most k. Thus
```
XY ≤ k X + s k².
```
The unaggregated form, counting each anchor and both directions, is the kernel-checked pair_bound in Graph189CrossPort.lean.

Set x=X/k, y=Y/k. Suppose x≥c, where c≥2 and s≥c²+c. We have x²≤x+s since y≥x; as s/c≥1, (s/c)²−s/c−s≥0 yields x≤s/c. Factoring (x−c)(x−s/c)≤0 gives x+s/x≤c+s/c. Consequently x+y≤1+c+s/c. Restoring the s separator members and the possible exceptional vertex gives
```
n ≤ k(1+c+s/c)+s+1.
```

At c=3 and s≥14, the order bridge contradicts this bound. Indeed its right side is at most 2k+s(k+1)/2 whenever (s/6−2)k≥s/2+1. At s=14 this follows from k≥2s, and 2s(s/6−2)−s/2−1 is then increasing. At c=2+8/s and s≥24, the difference of the two coefficients of k is s/2+1−c−s/c=1−8/(s+4)−8/s>1/3. The difference exceeds the remaining cost s/2+1 since k≥2s. Also s≥c²+c as needed. This proves both pairwise bounds.

Let H count all high vertices outside S. The order bridge gives H>(2+s/2)k−s/2−1. At s≥15 this is ≥9k using k≥2s. At s≥24 it is also ≥3(2+8/s)k. If a component has at least the claimed threshold L, the rest has fewer than L high vertices by the pairwise conclusion, and such a component is unique. Otherwise group components one at a time until the total first reaches L. This group has fewer than 2L high vertices and the rest has at least L, contradicting the same conclusion. This proves (3). The roots attaining threshold values and the 1 for the possible global low were retained in these inequalities.
