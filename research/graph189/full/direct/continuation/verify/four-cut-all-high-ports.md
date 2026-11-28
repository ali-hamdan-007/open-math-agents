# Four-connectivity when every high vertex outside the separator is a port

Suppose a qualifying graph has a minimum four-cut S separating two components and every high vertex outside S has an S-neighbor. The graph is traceable for k≥16. A unique low vertex may lie anywhere, including as a nonport. This is complementary to the high-nonport-on-both-sides theorem.

Otherwise n≥6k−10 by the moderate-order theorem. Write a≤b for the high-port counts on the two sides, named A,B respectively. Then a+b≥6k−15. Every anchor contacts both sides and has at most k neighbors on either side, by the even quota at an opposite contact. For every port x on A with r incident anchors, the boundary of its closed A-neighborhood has size at least four. Hence x spends at least 4−r even places outside B. This holds at low and high ports alike.

Here b≥(6k−15)/2>2k. Consequently no A port is universal to S: such a port alone would see all b opposite high ports at even distance. For each anchor use any A contact, necessarily of support at most three. Its even set therefore bounds the number of B contacts at that anchor by k−1. An A port meeting exactly three anchors sees all high B ports except those exclusively at the fourth; it also spends one even slot outside B. Thus b≤2k−2 if a three-anchor A port exists, which is impossible. Now every A port has support at most two. A two-anchor A port would give b≤(k−2)+2(k−1)=3k−4 by the same argument.

Every high A/B port pair is at distance two, three or four. On a three-edge geodesic an anchor has distances one and two from the ends. Every incidence of an anchor at distance two from a high port consequently accounts for at most k cross pairs, by the bound on opposite contacts. There are at most 4k such incidences by the anchor budgets. As in global/cut4/cross-port-pairs.md, reserving 4−r even slots outside B at the A end gives the following two alternatives.

* If b≤3k−4 then ab≤(k−2)a+4k². But a≥6k−15−b, and (6k−15−b)(b−k+2)>4k² throughout (6k−15)/2≤b≤3k−4. The left side is concave. Its difference from 4k² at the two endpoints is respectively 2k²−63k/2+165/4 and 2k²−28k+22. Both are positive for k≥16.
* If b≥3k−3 then every A port is private. Each B contact class has size at most k−3, so b≤4k−12 and ab≤(k−3)a+4k². Now (6k−15−b)(b−k+3)>4k² on 3k−3≤b≤4k−12. The endpoint excesses are 2k²−24k and 2k²−27k+27, positive for k≥16.

Both alternatives are impossible.

The general product observation uses all high vertices, with X≤Y their counts on the two sides of a minimum s-cut. Each cross high pair at distance three can still be assigned to (anchor, high side vertex at exact distance two), even if one endpoint is a nonport. Hence XY≤kX+sk². Summing the closed-neighborhood boundary reservations on the smaller side gives XY≤(k−s)X+Σ|N_S(x)|+sk², where the sum is over its high vertices.
