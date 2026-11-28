# Eliminating maximum degree from the retained-width inequality

Write m=n−2k and e=Δ−k. In every Graph 189 counterexample with n≥6k+2 the following integer inequality is necessary:

    (k−1)(m−1)(3m−k−1) ≤ k(k+1)(2k²+m−k−1).

Indeed the rooted local Ore bound gives e≥e₀=(m−k−1)/k. The maximum-degree lemma gives e≤2k. The local degree-width incidence inequality from ../root/maximum-degree-width.md gives F(e)≤0, where

    F(t)=(m−t−2)(2m+kt)−k(k+1)(2k+t).

This polynomial is concave since its leading coefficient equals −k. At m≥4k+2 we have F(2k)>0, because the positive product there is at least 2k(8k+4+2k²)>4k²(k+1). Thus F(e₀)≤0 by concavity, since both endpoint values positive would imply positivity everywhere in the interval. Multiplying by k and factoring m−e₀−2=(k−1)(m−1)/k gives the formula.

It follows directly that along any hypothetical sequence with unbounded k, the upper limit of n/k^(3/2) is at most √(2/3). For subsequences bounded away from zero the existing universal order upper makes m comparable to k^(3/2). The displayed necessary inequality then gives 3m²≤(2+o(1))k³ by division by k. Subsequences with n<6k+2 contribute zero in the limit.
