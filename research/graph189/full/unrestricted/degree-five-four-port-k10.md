# The four-port branch is traceable for k≥10

Use the same setup and initial neighborhood bounds as in degree-five-four-port-overlap.md: P has four ports, R is wholly in layer three, h≥2k−3, |S_p|≤k−1, and at most 3−c_p members of R are at even distance from p, where c_p is the number of other ports at distance two. The latter budget covers B_p, and also the union of S_q−S_p over all ports q adjacent to p. The graph Q links ordinary port neighbors and pairs sharing an R-neighbor. An overlap across ordinary port-adjacency components satisfies |S_p∩S_q|≥k−5 and |S_q−S_p|≤4. In greater detail, for any common neighbor x, writing j=|N_P(x)|, all its R-neighbors outside that intersection lie in B_p∪B_q, giving

    |S_q−S_p| ≤ j−2+|B_p|+|B_q|.

In this formula and below the port labels may be interchanged. We suppose k≥10.

## Q cannot be connected

Between different ordinary adjacency components, one overlapping port pair forces every cross-pair of those components to overlap. Indeed, across an ordinary edge at most three elements of a neighborhood disappear, while the existing intersection has at least k−5>3 elements. Iterate along ordinary paths on both sides. Moreover when three different ordinary adjacency components form a chain of overlap links, the outer pair also overlaps: from the first consecutive pair's intersection of size at least k−5, at most four members of the middle neighborhood are missed by the third, and k−5>4. Iterating shows that in a connected Q every two ports in different ordinary components overlap. Thus each port in an ordinary component of size s counts all 4−s external ports in c_p.

If ordinary adjacency is connected, take a connected dominating set of size at most two (the internal vertices of a spanning tree on four vertices). For adjacent dominating ports p,q, the union of the sets of p and its neighbors has size at most |S_p|+3; all remaining neighbor sets of q add at most three beyond S_q. One dominating port also suffices in a star. This gives h≤k+5. The same bound holds for every disconnected ordinary partition, still assuming Q connected:

* For (3,1), choose the center of the connected triple. Its ordinary neighbors together add at most two outside its neighborhood, since c≥1 at the center. The outside singleton may then add at most four by overlap.
* For (2,2), each port has c≥2. One intercomponent overlap adds at most four, and each ordinary edge adds at most one.
* For (2,1,1), begin with one singleton and add the other. Both have c=3 and B empty, so their overlap link adds at most two by the formula above. One port of the pair adds at most three by the same formula, since its boundary has size at most one. Its ordinary mate adds at most one.
* For (1,1,1,1), every boundary is empty, so each of three overlap links adds at most two.

In all cases h≤k+5<2k−3. Therefore Q is disconnected.

## Two port pairs

If Q has two components of size two, split R into H_1,H_2 according to the pair containing the nonempty port-neighborhood of each vertex. Write L_i for H_i together with its two ports, and N=|L_i|. By the ordinary or overlap link bounds, |H_i|≤k+3, N≤k+5, and each port misses at most four members of H_i. For any x∈H_i, choosing an incident port p shows that every neighbor of x across the partition belongs to B_p. Hence d_L(x)≥k−3. At most six vertices of H_i have any cross-neighbor, since each such vertex belongs to the union of the two boundaries of the opposite port pair. All other core vertices have degree at least k internally.

In L_i with a degree-two marker at prescribed endpoints, the cycle-closure threshold is N+1. Each port has at least N−6 core neighbors; each core vertex has degree at least k−3≥7, hence every missing port-core edge closes. The two ports can now be linked as well (N≥5 since a core vertex initially has at least seven internal neighbors). An original core vertex of degree at least k becomes complete to all original vertices since k+(k−3)≥N+1. At most six original vertices remain, each now adjacent to at least N−6 original vertices and having degree at least seven. If N≥13, 2(N−6)≥N+1; if N≤13, 2·7≥N+1. Thus the originals become a clique. Removing the marker after reversing cycle closure gives Hamilton-connectedness of L_i.

Connectedness of D supplies a cross-edge ab between the two blocks. End the shell path at an anchor of a port of L_1 different from a, span L_1 to a, cross to b, and span L_2. All edges used on the reversed paths are original.

## An isolated Q port

Let p be isolated and X=S_p. Its vertices are private. This set is nonempty since p has degree at least k≥10 and at most five neighbors outside R. Every x∈X has at most |X| neighbors in X∪P, and every other neighbor belongs to B_p, of size at most three. Thus |X|≥k−3. Each x needs at least one such neighbor since |X|≤k−1. If y is that neighbor, a port q touching y has x∈B_q. Consequently, with C=∑_{q≠p}c_q,

    k−3 ≤ |X| ≤ ∑_{q≠p}|B_q| ≤ 9−C.

Thus |X|≥7 and C≤2. In particular there cannot be two isolated ports: their two disjoint private sets would contain at least fourteen vertices, whereas every private vertex lies in the union of all four boundaries, of total size at most twelve. (The same outside-neighbor argument applies to every private vertex.) Therefore the three remaining ports form a connected Q component.

These three ports also have connected ordinary adjacency. Three ordinary singletons would need at least two distinct nonadjacent overlaps to connect them, costing at least four in C. For a pair and a singleton, the needed external overlap propagates across the pair's ordinary edge, again giving at least two distinct nonadjacent overlaps. Both alternatives contradict C≤2.

We claim that H=R−X is the single neighborhood S_q of a port q adjacent to both its mates. If C≤1, ordinary adjacency of the triple is a triangle, since two nonadjacent endpoints of an ordinary three-vertex path each count the other. By |X|≥7 and its cover by the other three boundaries, some q has at least three members of X at distance two. This exhausts its allowed budget in R; any vertices in its two mates' neighborhoods outside S_q would also be at distance two, but lie outside X. Hence H=S_q. If C=2, all inequalities above force |X|=7 and the seven available R-even slots of the other three ports are already filled by distinct members of X across them. Each is saturated. Choosing the middle port q of the connected triple (any port in a triangle) gives H=S_q by the same argument.

The singleton block X∪{p} has at most ten vertices, with p universal and each x retaining degree at least k−3≥7. It is Hamilton-connected by the marked degree-sum criterion. In the other block L=H plus the port triple, N=|L|≤k+2. Each core vertex loses at most three cross edges, by its own incident port's boundary. Every port misses at most three vertices of H, since it is either q or adjacent to q, and has at least one port neighbor inside the block. Its internal degree is thus at least |H|−3+1=N−5. Every core-core and core-port pair meets marked threshold N+1, using 2(k−3)≥k+3 and (N−5)+(k−3)≥N+1. After these closures the remaining port pairs have endpoints adjacent to all N−3 core vertices. For N≥7, 2(N−3)≥N+1. Indeed N≥8 since every core vertex retains at least seven neighbors. This proves Hamilton-connectedness of L. The connected D has a cross-edge whose endpoint in X∪{p} belongs to X. Route from the shell through p across the singleton block, across that edge, and through L to finish.

Thus the full (4,4) case has at most the finite residual 7≤k≤9 and 2k−3≤h≤2k+4, at most 24 parameter pairs with n≤37. The upper bound holds since all private vertices belong to the four boundaries and 2h−12≤∑|S_p|≤4(k−1).
