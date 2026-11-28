# The one-third-connectivity range using linked sets and the width bound

Assume the original Graph 189 hypotheses, write k for the second-smallest degree, and suppose k≥19 and 3κ≥k. One order comparison rules out a counterexample throughout this range. It avoids the block and endblock calculations in the earlier high-connectivity proof. This is a paper consequence of the graph-facing inputs described below. The integration sources are being checked.

Put l=ceil(k/3). Then l≤κ and k≤3l≤k+2. Take a minimum-degree vertex z and assume the original graph has no Hamilton path. We get the same inequality in both alternatives:
`n≥(l+1)(k−l+2)−1`.

* If deleting z leaves a Hamiltonian path, take a longest path through z in the original graph. Let m be the size of its complement and u=k+1−m. Its exterior matching bound gives δ≤u and the displayed order at every parameter through u. Use l≤κ≤δ. The proof of this particular bound assumes δ≥3 and k≥5, both automatic here. It does not use the final structural conclusion.
* If deleting z leaves no Hamiltonian path, complete z to a universal vertex. The completion has minimum degree at least k and connectivity at least κ. Every longest cycle leaves a linked set of at least l+1 vertices. The native minimum-deletion proof needs 3≤l, 3l≤k+2, 2l+2≤k and 6≤k. All hold here. The linked-set theorem in @koolkao’s upstream PR 7971 therefore gives the displayed order. The full large-order threshold in that paper is unnecessary for this application.

For a compact arithmetic proof, set
`F(k,n,e)=(n−2k−e−2)(2(n−2k)+ke)−k(k+1)(k+e)`.
When n≥4k+2 the actual maximum-degree width lemma gives F(k,n,e)≤0 at some 0≤e≤2k. Here e is the maximum-degree excess. The polynomial is concave in e, and is increasing in n on n≥4k+2 for this entire e interval.

For k≥26 put r=3l−k, which is 0, 1 or 2. Five times the displayed order lower bound, less k²+5k, is l²+lr+5l−r²+5≥0. In particular n≥6k, so A=(k−2)n−5k²+k≥0. The identity
`F(k,n,e)−F(k,n,0)=eA+ke(2k−e)`
implies F(k,n,0)≤0. On the other hand, both 5(n−2k−2) and 5(n−2k) are at least k(k−6). Thus 2(k−6)²≤25(k+1). This is impossible because the difference is (k−26)(2k+3)+125.

For 19≤k≤25 the values of F at e=0 and e=2k are already strictly positive at the least candidate order m=(l+1)(k−l+2)−1. The single use of concavity in e and monotonicity in n covers all larger orders. The finite check uses the seven exact pairs (k,l). The values are shown below.

| k | l | m | F(k,m,0) | F(k,m,2k) |
|---:|---:|---:|---:|---:|
| 19 | 7 | 111 | 3146 | 6984 |
| 20 | 7 | 119 | 3766 | 10246 |
| 21 | 7 | 127 | 4408 | 14026 |
| 22 | 8 | 143 | 8074 | 28402 |
| 23 | 8 | 152 | 9352 | 35572 |
| 24 | 8 | 161 | 10686 | 43614 |
| 25 | 9 | 179 | 16516 | 67366 |

The arithmetic and graph-facing integration are in Graph189ThirdWidth.lean, Graph189ThirdFinite.lean and Graph189ThirdConnectivity.lean. This argument does not address the low-connectivity or remaining small-degree formalization obligations.
