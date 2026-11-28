# Traceability at connectivity at least one third of the second-smallest degree

Every finite connected graph satisfying the Graph 189 condition with vertex connectivity s≥ceil(k/3), where k is its second-smallest degree, has a spanning path. There is no bound on the maximum degree or any requirement on the possible single low vertex.

Degrees k≤15 follow from the already audited fixed-degree theorems. Larger connectivities covered by the preceding half-connectivity theorem allow us to suppose s≤floor(k/2). Write h=ceil(k/2), and use the optimized longest path P and smallest high-bearing exterior component C of the exterior results. The global geodesic order bound (../../lowblock/geodesic-width-and-order.md) is

    n ≤ 2k+1+floor(sqrt(k²(k+1)+1)).

If C is 2-connected with m≤2q−1, where q is its minimum internal degree among high members, then its largest contact matching has size j≥s. This contradicts 3j<k from local-cover-contacts.md. In the other 2-connected case or the large-endblock case, the established cycle packing bound is at least (s+5)q+2s−1 with q≥h; an endblock gains a further h−3. A smaller endblock instead requires n≥3h−1+min((h+1)(k−h+2),(s+1)(k−s+2)), by ../k10/uniform-matching.md.

For k≥25 we have (k+6)²−36(k+1+1/k²)=k(k−24)−36/k²>0, giving the simpler upper n≤k²/6+3k+1. The large-block lower is at least k²/6+19k/6−1, which exceeds the upper bound. For the small-block lower, the quadratic (x+1)(k−x+2) is increasing up to x=(k+1)/2. Both s and h lie between k/3 and this point. Thus

    n ≥ 3k/2−1 + (k/3+1)(2k/3+2)
      = 2k²/9 + 17k/6 + 1
      > k²/6+3k+1.

For 16≤k≤24 all bounds are monotone nondecreasing in s through the range at issue, so evaluate at s=ceil(k/3). In either large-block case with even k we may replace q≥h by q≥h+1. Indeed q=h would leave at most one ambient distance-two vertex of C from a minimizing noncut high x by the optimized exterior inequality. A 2-connected block containing x can then have at most q+2 vertices, contradicting its required order of at least 2q−1. The two columns below give the exact geodesic upper bound and the smaller of the small-block and large-whole lower bounds with this refinement.

| k | Upper order | Lower order |
|---|---:|---:|
| 16 | 98 | 107 |
| 17 | 107 | 110 |
| 18 | 115 | 121 |
| 19 | 123 | 133 |
| 20 | 132 | 145 |
| 21 | 141 | 145 |
| 22 | 150 | 171 |
| 23 | 159 | 171 |
| 24 | 169 | 184 |

The lower bound exceeds the upper throughout, proving the theorem.
