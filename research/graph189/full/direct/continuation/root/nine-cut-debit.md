# A uniform obstruction on a minimum cut of size nine

For k≥163 there is no low vertex on a minimum nine-cut of a Graph 189 counterexample satisfying the established order, width, and cut inequalities. This applies in particular at k=175,176,177,178,183,184,185,186. Here k is the second-smallest degree, e=Δ−k, w is the basic root width, X≤Y are the two high populations, d is the loss at a putative low vertex on the cut, and r is the number of common labels of two neighbors on opposite sides.

The base order gives n≥10k−71>9k+8. Since d≥1 and kd≤2k+(k+1)r−n, the integer r≤9 must be nine. Also n≥8k+2 and 0≤e≤2k. Therefore 2(n−2k)≥e, so the raw width inequality gives w≥e. The width budget implies 4ke≤w(n−2k−e−2)≤k(k+e) and hence 3e≤k.

The cross product gives X(X−k)≤X(Y−k)≤9k². If 3X>11k then (3X)(3X−3k)>88k², contradicting this bound of 81k². Thus 3X≤11k.

With r=9 the mixed debit is 8(k−8)≤10k−n+X+9+9(e+8). Rearranging gives n≤2k+X+9e+145≤26k/3+145. Combining this with n≥10k−71 forces k≤162.

After the zero-deficit lift n≥11k−89, the entire range 163≤k≤192 is excluded without checking individual degrees. The rooted order bound n≤3k+1+ke gives e≥8 by integrality. The same width argument gives 3e≤k. Thus n−2k−e−2≥(81/10)k and 2(n−2k)≥(169/10)k. Multiplying the two raw width inequalities and using k+1≤193 and (k+1)/k≤101/100 gives
```
13689/100 + (81/10)e ≤ 193 + (101/100)e.
```
At e=8 the left exceeds the right by 61/100. The difference increases with e. These rational estimates avoid any reliance on the eight exceptional points of the compressed interval test.

The lift's numerical side conditions also hold here. The cross-order upper bound is n≤2k+1+9k²/(k−9). For k≥163 the last term is at most 10k, so 4n≤48k+4<k(k−1). With deficit zero, 2(k−1)>27 and floor((k−2)/2)+1≥10. The graph-theoretic lifted order follows from the separately cited removable-vertex and exterior-cycle argument.
