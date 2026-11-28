# Exclusion of the three-exception template for every k≥7

Assume the high-order, diameter-at-most-four, unique degree-five root setup of degree-five-connected-three-exceptions.md. If d=k−|L₂|=3 and s=|L₄|≤2, there is no qualifying graph for any k≥7. Together with the k=6 companion this eliminates that regime for all k≥6.

The established template has five anchors in a clique, three exceptional ports p₁,p₂,p₃ with disjoint nonempty anchor sets of sizes a₁,a₂,a₃ summing to five, and W consisting of k−6 vertices complete to all five anchors. Write R=L₃, h=|R|≥2k−s, and F=L₄. Let C be the union of all R-neighborhoods of W and put c=|C|, S_i=N_R(p_i), D_i=S_i−C, V_i=C∪S_i. The visibility set V_i and the two ports other than p_i are all at distance two from every anchor of type i. Consequently |V_i|≤k−2. The D_i cover R−C. Write σ_i=k−2−c−|D_i|≥0.

No w∈W can touch two exceptional ports. If it touches ports i and j and l denotes the remaining index, then at least h−c−|D_l|≥h−k+2≥k members of R−C are within their two supports and hence are at distance two from w. The vertex z gives an additional witness. Let w_i be the number of W vertices touching p_i. The sum of the w_i is at most k−6. Each w has a neighbor in C, since otherwise it can have neighbors only among the five anchors and |T|−1=k−4 other second-layer vertices, missing at least two exceptional ports. This would give degree at most k−1. In particular c≥1.

At p_i, the vertices z, the 5−a_i anchors of opposite types, and the k−6−w_i missed W-vertices lie at distance two. Thus there are at most a_i+w_i remaining even slots. Their combined capacity over the three ports is at most k−1.

Call a vertex of R−C private if it touches only one exceptional port. The number b of such vertices satisfies

    b ≥ 2(h−c)−Σ_i |D_i| ≥ k+6−2s+c+Σ_i σ_i.

A private vertex on port i has at most |V_i|+s neighbors in V_i∪T∪F. If it has a core neighbor outside V_i, that neighbor is in some D_j for j≠i; then the private vertex is at distance two from p_j. For s≤1, the degree bound forces such a neighbor at every private vertex, contradicting b>k−1.

It remains to treat s=2. Call a private vertex on i neutral if it is not at distance two from either other port; write U for their set and u_i=|U∩D_i|. Every neutral vertex x on i is adjacent to all of V_i−{x} and both vertices of F, and |V_i|=k−2. Indeed x has no neighbor outside V_i in R, sees only p_i in T, and meets its degree requirement only at equality in |V_i|+2≤k.

Each of the two vertices of F has at least k−1 neighbors in R, larger than |V_i| for every i. In particular it has contacts in D_j from at least two different exceptional ports. The two vertices of F thus spend at least four of the combined unallocated slots at the ports. Every nonneutral private vertex spends a further slot. Hence

    |U| ≥ b−(k−5) ≥ c+7+Σ_i σ_i.                      (1)

Every w sees every member of U at distance two through a C-neighbor, as each neutral vertex meets all of C. The vertex w also sees z and at least two missed exceptional ports at distance two, so k≥c+10≥11.

Some w must touch an exceptional port. Otherwise the residual capacity over all ports would be only Σa_i=5, with at least four slots spent on F. This would give |U|≥b−1≥k+1+c, impossible at any w.

If w touches p_i, then all of D_i and all of U−D_i are distinct from w and at distance two from it, in addition to z and its two missed ports. Thus

    u_i ≥ |D_i|+|U|−(k−3) = |U|−c+1−σ_i ≥ 8.         (2)

There cannot be a neutral vertex x of a different type j. Such an x would see those eight or more neutral vertices in D_i at distance two through F, because x has no neighbors outside V_j in R and neutral vertices of different types are not in V_j. It also sees all k−6 members of W via C and the a_j anchors of its own port. This exceeds k. Thus there is a single neutral port index i, and the only exceptional port that can be touched from W is p_i by (2). Denote the remaining indices by j,l.

Neither p_j nor p_l is adjacent to p_i: such an adjacency would put all u_i≥8 private neutral vertices at distance two from that opposite port, whose residual capacity is only its anchor multiplicity since it has no W contact.

Let Y=R−V_i, so |Y|≥(2k−2)−(k−2)=k. At most 6−a_i vertices of Y can be at distance two from p_i. To see this, fix a neutral vertex x on i. Every two-step path from p_i to Y must use a member of V_i as its intermediate vertex: anchors have no edges into R, W has no contacts in Y, and the other exceptional ports are not adjacent to p_i. Since x misses Y and meets V_i−{x}, every such Y vertex is at distance two from x. The k−6 members of W and the a_i relevant anchors are additional even witnesses at x. This proves the bound.

On Y only ports j,l can occur. The number b_Y of private members of Y satisfies

    b_Y ≥ 2|Y|−|D_j|−|D_l| ≥ 4+2c.                    (3)

None is neutral. At most 6−a_i can be counted at p_i. The combined available capacity of p_j,p_l is a_j+a_l=5−a_i, and each of the two fourth-layer vertices is already counted at at least one of these ports. Therefore

    b_Y ≤ (6−a_i)+(5−a_i−2)=9−2a_i.                  (4)

Equations (3)–(4), with c,a_i≥1, force c=a_i=1; hence 6≤b_Y≤7. If p_j,p_l are adjacent, every private member of Y is at distance two from the other of those two ports, but their combined capacity after the F witnesses is at most two. If their supports in Y are disjoint, every member of Y is private, contrary to |Y|≥k≥11. In the remaining case they are nonadjacent with an overlap, so each counts the other at distance two. This spends two further slots, reducing the upper bound (4) from seven to five. The contradiction proves the theorem.
