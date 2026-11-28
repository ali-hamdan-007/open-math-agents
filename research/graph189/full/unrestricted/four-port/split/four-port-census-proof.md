# Four-port exclusion for second-smallest degree 6 through 9

**Theorem.** In a qualifying graph with a unique vertex z of degree five, disconnected G−N[z], and the two-component configuration (a,s)=(4,4), the order is at most 3k+2 for each k∈{6,7,8,9}.

In this configuration the shell consists of z, its five anchor neighbors A, and a (k−4)-clique K complete to A. The other component D has four ports P and a third layer R; no fourth layer occurs. Every x∈R has a nonempty port neighborhood and all its neighbors belong to D. Suppose n>3k+2. Then h=|R|≥2k−3>k, since n=k+6+h. Each vertex other than z has degree at least k and each vertex counts at most k vertices at positive even distance.

## Finite verification

The replay source is four-port-census.cpp (SHA-256 bbe3f1311db27041aad09aa483df08c7fda72fdc3df1ce4837f4b3de14e17e5f). Build with c++ -O3 -std=c++17 four-port-census.cpp -o four-port-census and run with each of the four integer arguments. The exact standard outputs are census-k6.log, census-k7.log, census-k8.log, and census-k9.log. No solver or external data is used.

1. Enumerate the subset I(a) of ports touching each of the five anchors. Every port touches an anchor. No set I(a) can be all four ports since the whole third layer would then lie at distance two from a. Anchor permutations allow the five sets to be sorted; port permutations allow retention of the least sorted tuple. This gives 546 tuples. Try all 1,024 anchor graphs and all 64 port graphs for every tuple.

2. Let S_p denote the neighbors of p in R. For anchor a, let m_a count its missed anchors and v_a its missed ports reachable in two shell edges. A member of the union of S_p over p∈I(a) is at distance two from a, giving the bound k−m_a−v_a on that union. The union is also bounded by k−1, since at least one of these missed-anchor or missed-port witnesses exists. Indeed, if a sees every other anchor, it sees a missed port in two edges through that port's anchor. Require also d_A(a)+|I(a)|≥3, because z and K give a exactly k−3 other neighbors.

3. Write s_p for the upper bound on |S_p| inherited from these anchor constraints, and impose the lower bound k−d_A(p)−d_P(p). The port sees all of K and z at distance two. Subtract from the other three slots the number of nonneighbor anchors and other ports already reached in two edges within A∪P, leaving b_p≥0 slots for potential further witnesses. In particular at most b_p vertices of R can be at distance two. Thus the union of S_p and the supports of its ordinary port neighbors has size at most s_p+b_p.

4. Propagate the union bounds to smaller subsets by inclusion, and bound unions of disjoint subsets by sums. To bound the number w of vertices with just one port (private vertices), note that private x∈S_p needs a neighbor y∈R−S_p because |S_p|≤k−1. This y is at distance two from p; it meets a port q≠p, which in turn sees x at distance two. Hence w≤Σb_p. Further, a private x on p can have at most s_p+b_p neighbors, so w is at most the sum of s_p over ports with s_p+b_p≥k. With 2h−w≤Σs_p, these private bounds give two more bounds on h. For each k, only 38 shell records have final upper bound h=2k−3 and 26 have final upper bound h=2k−2; all remaining records have lower upper bounds. The initial unrestricted private bound also gives h≤2k+4, the last row shown by the replay.

5. For every retained shell and permitted h, enumerate the nonempty port neighborhoods M_x of each x in sorted order. Check the support lower bounds and all union upper bounds. Subtract from b_p any newly discovered distance-two ports via common R-contacts. A missed vertex x is a mandatory distance-two witness of p if M_x contains an ordinary port neighbor of p. Check these capacities and the total private-vertex bound.

6. Enumerate Z_x, the set of ports at distance two from x, sorted within equal M_x classes. It is disjoint from M_x, contains the mandatory ports in step 5, and must be nonempty at a private x. At each p, every membership in a Z_x consumes a slot. For a proposed assignment, make all possible core edges xy satisfying

       M_x ⊆ M_y∪Z_y      and      M_y ⊆ M_x∪Z_x.

   These conditions are necessary: a port of x missing y reaches y in two steps via x. Retain the actual port adjacencies and port–core memberships. This gives a graph containing every feasible D with this type assignment. Reject it if a core vertex has degree below k or if it is disconnected.

The exact counts are the same for each of k=6,7,8,9:

| h | Shells with maximum h | After masks | After distance-two sets | After core degrees | After connectivity |
|---|---:|---:|---:|---:|---:|
| 2k−3 | 38 | 36 | 266 | 0 | 0 |
| 2k−2 | 26 | 4 | 4 | 4 | 0 |
| ≥2k−1 | 0 | 0 | 0 | 0 | 0 |

The first column of counts describes each shell's upper bound; in evaluating a given h, every shell whose bound is at least h is examined. No feasible D survives. This proves the theorem.

For k=6 there is also a distinct three-component possibility outside (4,4). It is traceable by the two-port construction in degree-five-k6-components-shell.md. The two- and three-port manuscripts handle the other two-component parameters. For k≥7 the structural component lemma gives exactly two components when the closed-neighborhood complement is disconnected. This census itself makes no claim for k≥10 or for a connected closed-neighborhood complement.
