# Traceability at one fifth connectivity, and at every degree through 25

Let G be a finite connected graph with second-smallest degree k and at most k other vertices at positive even distance from each vertex. Then G has a spanning path whenever 5κ(G)≥k. Separately, it has a spanning path without any connectivity restriction when k≤25.

For k≤18 use the preceding fixed-degree results. For 19≤k≤25 and connectivity at least five use five-through-25.md. At connectivity at most four the general four-cut results complete all these degrees. The four-cut proof uses ../../verify/four-cut-deep-all-sizes.md, ../../order/four-cut-shallow-common-anchor.md, ../../order/four-cut-shallow-sole-nearest.md and ../../global/cut4/no-singleton-large-side.md, with the extra-component analysis in ../../verify/four-cut-three-components.md at the smaller degrees and the earlier results for smaller connectivities. These arguments give the second assertion, including the boundary case k=20 and κ=4 in the first assertion.

Now assume k≥26, write s=ceil(k/5) and suppose the true connectivity is at least s. As in the prior papers let h=ceil(k/2), U=2k+1+floor(sqrt(k²(k+1)+1)), and choose a smallest high-bearing component C exterior to an optimized longest path. If C is 2-connected and near-Hamilton-connected, its maximum contact matching j and order m obey s≤j, 3j<k, m≥k−floor(j/2)+2, and n≥(j+2)m+j−1. In the large whole or endblock cases the ordinary lower bound is at least (s+5)h+2s−1. In a small endblock the lower order is at least 3h−1+min((h+1)(k−h+2),(s+1)(k−s+2)).

For k≥100 we have sqrt(k+1+1/k²)<k/10+1/2: after squaring, k²/100−9k/10−3/4−1/k²>0. Thus U<k²/10+5k/2+1. The large-block lower order is at least k²/10+29k/10−1. The small-block lower is at least 4k²/25+27k/10+1 because (x+1)(k−x+2) is increasing from k/5 through (k+1)/2. In the near case m>5k/6 and j≥k/5, hence n>k²/6. All three lower bounds exceed U.

For the remaining 26≤k≤99, fifth_range.py carries out the exact same comparisons and large-block refinement as five-through-25.md. There is no near-Hamilton-connected candidate. For small endblocks check b≥h+1 and J≥max(s−1,k−b+1) in the lower bound n≥(J+2)b+3h−1. The only surviving (k,b,J) is (30,26,5). Every high noncut of this terminal block needs five marks and all of its 25 internal neighbors. The five real marks must be the entire cover. The noncuts therefore form a clique complete to the five marks and the articulation. Any one of them has degree 30 and a six-neighbor cover of its second layer. Its rooted order is at most 1+60+6·25=211, whereas the endblock lower requires 226.

The large good block arithmetic of five_blocks.py is unchanged except for the lower connectivity s. There are only 133 residual tuples across the entire 74-degree interval. Their positive certified order margins are shown for the only ten degrees with any such tuple.

| k | s | Residual tuples | Minimum excess over U |
|---|---:|---:|---:|
| 27 | 6 | 2 | 26 |
| 28 | 6 | 8 | 14 |
| 29 | 6 | 20 | 13 |
| 30 | 6 | 43 | 11 |
| 32 | 7 | 1 | 41 |
| 33 | 7 | 5 | 26 |
| 34 | 7 | 15 | 25 |
| 35 | 7 | 36 | 24 |
| 37 | 8 | 1 | 60 |
| 40 | 8 | 2 | 59 |

Run python fifth_range.py to repeat the small and near tests and regenerate fifth_range.log. The additional large-block computation only considers the sizes of the certified neighborhood extensions and their degrees. Every remaining necessary exterior alternative contradicts the order bound, completing the first assertion.
