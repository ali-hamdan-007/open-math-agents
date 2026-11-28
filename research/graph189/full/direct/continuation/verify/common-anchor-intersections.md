# Common separator neighbors and the asymptotic connectivity

Consider any sequence of counterexamples to Graph 189 with cut size s tending to infinity. Write k for second-smallest degree. Then

    s²/k → 1,   n/(k√k) → 1.

If a minimum-degree vertex belongs to a minimum separator, its degree satisfies δ≥k−O(1) uniformly over the sequence. The same near-regularity assertion is not needed when it belongs to no minimum separator.

Let S be any minimum separator, with two components A,B and A the smaller high side. Use the mixed incidence estimates in ../lowblock/mixed-anchor-blocks.md. They hold for all placements of the unique possible low vertex and for each choice of high reference vertex a∈A. Put T=N(a)∩S, Q_i=N(i)∩B, R_i=N_B(Q_i) outside Q_i. Then Σ_{i∈T}|Q_i|=O(k), and the sum of the excess multiplicities of the R_i for i∈T is O(k). Both constants are uniform in a and S.

For any high b∈B write W=N_B[b] and J=T∩N(b). For every i∈J its contact b lies in Q_i, so W⊆Q_i∪R_i. Counting all copies in W gives

    |J||W| ≤ Σ_{i∈T}|Q_i| + |W| + O(k).

The final term bounds repetitions of the R_i. Since |W|≥k−s+1=(1−o(1))k, we conclude |J|=O(1). This holds for every crossed high pair.

Suppose the unique low z belongs to S and choose its neighbors a,b on opposite sides by inclusion-minimality. The open neighborhoods of a and b have intersection J, since there are no edges between sides. Adding a and b gives a set of at least 2k+2−|J| vertices at distance at most two from z. The even cap bounds this ball by 1+δ+k. Hence δ≥k+1−|J|=k−O(1).

The cutoff in ../global/arity/three-common-labels.md gives n<(s+1+3/(s−2))k+2s+3 in a counterexample for large s. If a minimum-degree vertex belongs to no minimum cut, ../root/universal-minimum-order.md gives n≥(s+2)(k−s+1)−1. Otherwise δ≥k−O(1) as above, also true when all vertices are high. The removable-vertex proof ../global/arity/critical-removable-vertex.md with this value of δ gives n≥(s+2)(k−s−O(1))−1. Here its independent-exterior alternative costs n≥k(k−1)/4, excluded since s=O(√k); otherwise its surviving exterior cycle has at least s+1 vertices, allowing Nikoghosyan’s corollary at s+1 as in the cited proof. Comparing the two bounds gives k≤s²+O(s)+O(k/s). Combined with the known s≤(1+o(1))√k, this yields s²/k→1. The universal minimum-order bound and n≤2k+1+floor(sqrt(k²(k+1)+1)) then sandwich n/(k√k) between quantities tending to one.

The coordinator and the independent reviewer derived the window count separately.
