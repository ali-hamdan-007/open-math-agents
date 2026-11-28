# Inheriting the even cap across a separator

Let G be qualifying, with second degree k. Let A and B be anticomplete nonempty parts separated by S, each anchor i∈S touching both parts. Assume G[B] is connected and its vertices are all high in G. Write P_i=N_A(i), Q_i=N_B(i), p_i=|P_i| and q_i=|Q_i|. Suppose d_B(x)≥k−s_B for every x∈B. For each i assume some A-neighbor has at least k−s_A neighbors inside A. Put ε_i equal to the number of vertices outside B at positive even distance from i. Since the closed internal neighborhood of the chosen A-neighbor lies in P_i together with even-distance witnesses in A, we have ε_i≥k−s_A+1−p_i.

## Two-edge transfers are automatic for small separators

Nonadjacent a,b∈Q_i have their B-neighborhoods inside (B₂^G(i)∩B)∖{a,b}, whose order is at most q_i+k−ε_i−2. They thus have a common B-neighbor whenever

    q_i≤k−2s_B+1+ε_i,

in particular whenever q_i≤2k−2s_B−s_A+2−p_i. Independently each a∈Q_i spends p_i positive even places on all P_i, and all its missing other Q_i members are also at distance two via i. Thus it misses at most k−p_i other Q_i members. If nonadjacent a,b in Q_i had no common Q_i-neighbor, their two missing-sets together would have at least q_i incidences: each other point is missed by at least one and the two endpoints miss each other. Consequently every such pair has a common neighbor if q_i>2(k−p_i). Also q_i≤k because any opposite P_i member sees all Q_i at distance two.

Take L=2s_B+s_A−2. If p_i≤k−L then the first bound holds even at q_i=k, and if p_i≥L then the two sufficient q_i ranges together cover all integers. Hence for k≥2L−1=4s_B+2s_A−5 every ambient distance-two path between B terminals can be replaced in B. This conclusion has no order bound. If each vertex has at most s actual separator neighbors and the relevant A ports are high, s_A=s_B=s works at k≥6s−5.

## Three-edge paths and an independent separator

Any ambient three-edge B-to-B path involving only one exterior point now transfers. If S is independent, this deals with all three-edge paths, since a length-three path with two outside points would need two adjacent anchors. Since B points are high, every originally odd pair in B was at distance one or three. Thus e_B(x)≤e_G(x) minus all x's outside positive even witnesses. If each x has at least s_B such witnesses, then e_B(x)≤k−s_B≤δ(B), and B is itself qualifying. In a minimum counterexample this yields a path spanning B irrespective of its order.

In particular take s=3, k≥9, independent S, δ(B)≥k−2, and at least one high A-neighbor at each anchor (so its internal A degree is ≥k−3). The transfer threshold applies with s_B=2, s_A=3. If p_i≥2 for every i, every B port sees at least two opposite-side A members at distance two. If A has a high nonport, every B nonport sees this opposite nonport at distance four by the high-pair bound, and also has an anchor at distance two provided it has depth two from S. More generally if a B nonport has S-depth three or more it would be at distance at least five from that opposite high nonport, impossible. Therefore every B point has at least two outside even witnesses, so B qualifies and is traceable in a minimum counterexample. In the smallest-fragment, high-order deep cut branch, the hypotheses p_i≥2 and the stated improved B minimum degree may be supplied by the separate fragment and port-degree theorems. This proof does not assume that the inherited spanning path has an endpoint at an anchor.

For a possibly nonindependent S, consider an ambient geodesic x,i,j,y with x,y∈B and i,j∈S. Here x∉Q_j and y∉Q_i. The d_B(x) B-neighbors of x and all q_j B-contacts of j lie in (B₂^G(i)∩B)∖{x}, of size ≤q_i+k−ε_i−1. Thus the first anchor can be relayed if q_j−q_i+ε_i≥s_B, and the direction can be reversed. Any failed transfer requires both

    ε_i+q_j−q_i≤s_B−1,   ε_j+q_i−q_j≤s_B−1.

In particular ε_i+ε_j≤2s_B−2, and hence p_i+p_j≥2k−2s_A−2s_B+4. Its two endpoints x,y must both be ports. For the transferred-distance argument at deep points it therefore suffices to check the two-edge transfer alone.

## All anchor graphs for three-cut sides, including failed three-edge transfers

Suppose now |S|=3, s_A=3, s_B=2, and k≥12, with the A-contact and B-degree assumptions already stated. Call an anchor edge ij faulty if both of the necessary failure inequalities above hold. Then ε_i+ε_j≤2, |q_i−q_j|≤1, and p_i≥k−2−ε_i≥k−4 at every incident anchor. Since i,j are adjacent, each P_i member missing j at distance one sees j at distance two via i; in other words P_i∖P_j is in j's even set outside B. Thus |P_i∖P_j|≤ε_j. All anchors incident to faulty edges have a common A-neighbor: the graph of these edges on at most three points is connected, and one can start at an anchor incident with every other one. Along each of at most two incident edges at most two A points can be lost, fewer than its p_i≥k−4 points. This common A member sees every point in the union Q of the participating Q_i at distance two, so |Q|≤k.

A B-point with no new even partners on passing to B spends only its old even budget. Consider x with a genuinely new even partner. Its old odd distance was three, so there is a path x,i,j,y through a faulty edge of S, where x touches i and misses j. Fix this i,j. All new partners of x belong to Q and none to Q_i, since any Q_i partner already had original distance at most two and an original distance-one edge survives. Hence their number g(x) is at most k−q_i. The other two possible Q sets have total size at most (q_i+1−ε_i)+(q_i+2−ε_i), because j's contact count is at most q_i+1−ε_i and the third anchor is adjacent to i or j in the faulty-edge graph if present. Its increase across the next edge is at most one. Thus

    g(x)≤min(k−q_i, 2q_i+3−2ε_i)≤p_i−1.

Indeed q_i≥3+ε_i gives the bound k−3−ε_i≤p_i−1. Otherwise the second expression is at most seven, and p_i−1≥k−3−ε_i≥7 for k≥12. On the other hand x sees all p_i opposite A contacts and the missed anchor j at positive even distance outside B. Its original even cap k, after subtracting those p_i+1 witnesses and adding the at most p_i−1 gains, leaves e_B(x)≤k−2.

Consequently with each B vertex having at least two ambient outside even witnesses, B qualifies at k≥12 for an ARBITRARY three-anchor graph. In the deep all-high B setting these two exterior witnesses follow from p_i≥2 and one high nonport in A, as above. The corresponding spanning path in a minimum counterexample is unconditional in the size of B. Only the independent-anchor case needed the weaker degree threshold k≥9.

## A uniform bound for larger cuts

Let s=|S|≥2, retain s_A,s_B from the first section, write d=s_B≥1 and a=s_A≥1. Put c=a+2d−3 and C=c+d−1. Suppose

    k≥4d+2a−5,    k>s c,    k≥C+(s−1)(C+d−2).

For every B point having at least d original even witnesses outside B the number of positive even B-distance vertices is at most k−d. If every B point has this allowance, B qualifies. In particular for a=d=s≥3 the single bound k≥5s²−7s+2 suffices.

Only x with a new even partner needs further proof. All such partners come from failed x,i,j,y paths as above. Use the collection of all edges ij that actually occur for some such partner, directed with x touching starting i and missing j. A participating starting anchor i has p_i≥k−c since ε_i≤2d−2. All its P_i subsets consist of even witnesses of x, so their union has at most k points. Fix one starting anchor i₀. Moving from P_i₀ to another starting P_i loses at most k−p_i≤c elements; moving from a starting i to its adjacent end j loses at most ε_j≤2d−2≤c. The graph on all participating anchors with a star on the starts and these additional edges is connected, so use a spanning tree rooted at i₀. Across each of its at most s−1 edges in the indicated parent-to-child orientation at most c points disappear (one may attach each nonstarting end directly to one of its starts). The full intersection of these P sets has at least k−c−(s−1)c>0 vertices. A common member sees all participating Q sets at distance two, so their union has size at most k.

Choose a starting i maximizing q_i among starts. Any genuinely new partner misses i and lies in that union, so g(x)≤k−q_i. Every end anchor has at most q_i+d−1 contacts in B by the failure inequalities and the maximality of q_i. If q_i≥C then g(x)≤k−C. Otherwise g(x)≤(s−1)(C+d−2)≤k−C, since any new partner is in one of the at most s−1 end sets different from i. The outside witnesses from P_i and the missed anchor j give at least p_i+1≥k−c+1. Hence e_B(x)≤k−(k−c+1)+(k−C)=k−d. This proves the claim.
