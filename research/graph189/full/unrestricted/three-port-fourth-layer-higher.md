# The entire higher-order (4,3) case

**Theorem.** In the disconnected degree-five case (a,s)=(4,3), all orders above |R|=2k−2 are either impossible or traceable, for every k≥7. Together with the first-order theorem this closes the (4,3) parameter pair.

Let T be the third layer and H=|T|. Write f for the fourth-layer vertex when present. Thus R=T or R=T∪{f}. The sets S_p=N(p)∩T of the three ports cover T. The pure component K has k−4 vertices, all adjacent to every anchor. For each port p, the k−4 members of K and z lie at distance two, leaving at most three positive-even witnesses in D. Every member of B_p=N_R(S_p)−S_p lies at distance two from p, so |B_p|≤3. The set B_p can include f. When present, f has at least k neighbors, all in T.

## Saturation at an anchor

Suppose H>k. No anchor meets all three ports, since it would see all of T at distance two. For any anchor α, the union of the sets S_p of its incident ports has order at most k−1. Indeed it has one additional distance-two witness. If it misses another anchor, that anchor is a witness through z. Otherwise any missed port is a witness through a second anchor.

If some |S_i|=k−1, then H≤2k−2. Fix an anchor α of i. If α touches another port j, the anchor-union bound just proved gives S_j⊆S_i. The remaining port covers at most k−1 additional vertices. Otherwise α touches just i. If it were complete to the other anchors, each of the two other ports would be an additional distance-two witness, exceeding its cap. It must therefore miss another anchor β. Its quota is fully spent by S_i and β, so it misses exactly that one anchor and is at distance greater than two from both other ports. Each other port then has β as its sole anchor. Their joint core neighborhood has order at most k−1 by the bound at β. This again gives H≤2k−2.

At equality H=2k−2 with some |S_i|=k−1, both applications of the union bound force disjoint sets of order k−1. In either case there is a partition T=E∪V and a numbering of the ports p,q,r such that

    |E|=|V|=k−1,    E=S_p,    V=S_q∪S_r,    E∩V=∅.

In the first case p is the one remaining port and V=S_i∪S_j. In the second p=i. Every member of E has just one port neighbor.

## Counting private contacts

Suppose all |S_p|≤k−2. For a vertex x meeting only port p, the number of available neighbors in S_p∪P∪{f} is at most |S_p|+1≤k−1, allowing f even when present. Thus x has a neighbor y in T−S_p. Choosing a port q of y places x in B_q. The private-contact count X is at most 9, by summing the three boundary bounds. If f is present it actually belongs to at least two different B_p, as its k neighbors cannot fit in one S_p, giving X≤7.

By counting incidences, X≥2H−Σ|S_p|≥2H−3(k−2). When H≥2k−1 this gives X≥k+4>9. The saturation lemma ensures all |S_p|≤k−2 in that range, so H≥2k−1 is impossible regardless of f.

The only higher order left is |R|=2k−1 with f present and H=2k−2. If all |S_p|≤k−2 the private-contact bound gives X≥k+2>7, again impossible. Thus the partition E,V just proved is forced. Since f has at least k neighbors in T, it touches both E and V.

## Spanning paths at equality

Every x∈E has just the one port p. Its neighbors outside E∪P are in B_p, so d_E(x)≥k−4. Since 2(k−4)≥k−1=|E|, Dirac's theorem gives a Hamilton cycle in E. Breaking a cycle edge at any f-contact supplies a spanning E-path which can be entered from p and left through f.

First suppose q and r are nonadjacent. A vertex x∈V meeting one port loses at most one port neighbor and three external core neighbors when restricted to V. A vertex x∈V meeting both ports gives q and r another distance-two witness, namely each other. Its core neighbors outside V lie among the at most two remaining even slots at q. Again d_V(x)≥k−4. Dirac's theorem gives a Hamilton cycle in V.

Both q and r meet V. A port without a neighbor in T could have degree at least k≥7 only by meeting all five anchors and both other ports, contradicting their nonadjacency. On the Hamilton cycle of V there is an edge whose endpoints can be assigned distinctly to q,r. If a cycle vertex meets both, either incident edge works since its other endpoint is covered. Otherwise a cycle edge crosses between the two nonempty classes. Break the chosen edge to obtain a q-to-r spanning traversal of V. At least one of q,r forms a pair with p assignable to distinct anchors; otherwise all ports would have the same sole anchor, violating 2-connectivity. Label the good port q. Traverse r,V,q, the shell between its assigned anchors, p,E,f.

If qr is an edge, use the graph J induced by V∪{q,r}. Each x∈V loses at most three neighbors upon restriction to J: every outside neighbor lies in E∪{f} and is at distance two from a port of x. Each of q,r misses at most three vertices of V, since every missed vertex is seen at distance two through the other port. Including qr, each has at least (k−1)−3+1=k−3 neighbors in J. Thus δ(J)≥k−3 and 2(k−3)≥k+1=|J|. By Dirac, J has a Hamilton cycle. Break it at a port q that can be assigned an anchor distinct from an assigned anchor of p. The resulting J-path with endpoint q, followed by the shell, p,E,f, spans G.

The companion first-order proof deals with |R|=2k−2; smaller orders meet the established small-order bound.
