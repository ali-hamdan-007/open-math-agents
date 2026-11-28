# Order through four times the second-smallest degree at connectivity three

Suppose the finite connected graph G obeys the Graph 189 cap with k its second-smallest degree. If k≥13, κ(G)≥3 and n≤4k+1, then G has a Hamiltonian path. The graph may include a vertex of degree below k, and its maximum degree is unrestricted.

Assume otherwise and take a longest path P. By the [near-spanning theorem](../lowblock/all-near-spanning.md), P omits a component C containing a high vertex, where high means degree at least k. Put h=ceil(k/2). Recall that every high vertex has at least h neighbors in C and |C|≥h+1. A singleton containing a high vertex is impossible.

First produce a cycle disjoint from P of length d≥k−1. If C is 2-connected, write b=|C|. Were b≤k−2, delete its low vertex if present to get H of order at least b−1. Its minimum degree is ≥h−1 if a low vertex was deleted, ≥h otherwise. Consequently 2δ(H)≥|H|+1; H is Hamilton-connected by Ore's endpoint criterion. Each member has at least a=k−b+1 contacts on P, and |H|≥a since b≥h+1. In the contact bipartite graph a vertex cover of size <a leaves a member of H with an uncovered contact. Thus there is a matching of size a by König's theorem. Both tails and all the intervening gaps on P must contain at least |H| unmarked vertices, as otherwise a route through H between its prescribed contacts, or beginning at a prescribed contact on a tail, extends P. In particular

    n ≥ b+a+(a+1)(b−1) = b(k−b+3)−1.

The same bound holds if C has a cut vertex: choose an endblock B whose noncut vertices are all high (at most one low vertex, at least two leaf blocks). Put b=|B|. Each noncut vertex has internal degree ≥h in B and neighbors only in B and P. Hence b≥h+1. If b≤k−2, H=B minus its cut vertex has minimum degree at least h−1, and 2(h−1)≥b=|H|+1. Each H vertex has at least a contacts on P, and the identical matching and gap count applies.

The concave polynomial b(k−b+3)−1 on [h+1,k−2] has its minimum at an endpoint. At b=k−2 it equals 5k−11, strictly above 4k+1 for k≥13. At b=h+1 it is (h+1)(floor(k/2)+2)−1, also above 4k+1, since h+1≥8 and floor(k/2)+2≥(k+3)/2. This rules out b≤k−2. In either the whole 2-connected component or the good endblock, all but at most one vertex have internal degree at least h. Fan's circumference theorem supplies a cycle of length d≥min(b,2h)≥k−1.

Choose three vertex-disjoint connectors from the cycle to P by Menger's theorem. Each tail of P uses at least d vertices outside its marks; each of the two inner gaps uses at least ceil(d/2)+1 by the longer cycle arc between its prescribed endpoints. Adding the cycle and three marks gives

    n ≥ 3d+3+2(ceil(d/2)+1) ≥ 4k+1.

Equality requires d=k−1 even, n=4k+1, and every exterior vertex on the cycle. In particular C is 2-connected with a spanning cycle. The three connectors in this equality case are edges. There are spanning paths in C between all prescribed pairs except at most one [by the degree-two-marker closure argument](../lowblock/high-connectivity-complete.md), since |C|=k−1≤2h−1 and all but at most one vertex have internal degree ≥h. Among the two consecutive matched pairs at least one is good, as the three cycle terminals are distinct. Its gap therefore costs d vertices, strictly more than ceil(d/2)+1. This contradiction proves the claim.
