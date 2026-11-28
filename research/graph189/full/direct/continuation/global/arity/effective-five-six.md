# Effective degree ranges for the five- and six-connectivity theorems

The preceding papers five-cut-large-degree.md and six-cut-large-degree.md hold throughout **k≥210 at connectivity five** and **k≥1874 at connectivity six**. All graph and low-vertex hypotheses are unchanged. Here are the quantitative substitutions.

For s=5,6 and k≥100 the nontraceable order admits

    n ≤ (s+2)k + 1 + s²k/(k−s) ≤ (s+3)k.

Indeed for any minimum s-cut split take the smaller high-side count X. If this group is the single low vertex it touches all s anchors. The vertex and these anchors cover all opposite depths (at most four), giving n≤(s+1)k+s+1. Otherwise both groups contain a high vertex, so X≥k−s by degree. From XY≤kX+sk² we have X/k≤(1+sqrt(1+4s))/2. The convex upper bound n≤s+1+X+k+sk²/X attains its interval maximum at X=k−s or at the displayed upper endpoint. The former gives the first stated expression; the latter gives n≤s+1+(1+sqrt(1+4s))k, smaller here.

Take an optimized exterior good block with least nonexceptional interior degree q≥ceil(k/2). The neighborhood-packing lemma in global/two-thirds-exterior-degree.md, valid for an optimized high noncut vertex, gives either 3q>2k−3 or (q+1)(2k−3q+1)≤n+1. Hence q≥(2k−2s−4)/3 since (n+1)/(q+1)<2(s+3). In the five-cut range k≥210 the sharper order bound is n≤7k+27, so

    (n+1)/(q+1) ≤ 3(7k+28)/(2k−11) < 11.

Integrality now gives q≥(2k−9)/3. In the six-cut range k≥1874 one has n≤8k+38 and 3(8k+39)/(2k−13)<13, giving q≥(2k−11)/3. The alternative 3q>2k−3 entails both displayed improvements directly.

At five-connectivity the large-cycle alternatives therefore give n≥10q+9≥(20/3)k−21>13k/2+11. The small-block lower bounds retained in five-cut-large-degree.md exceed 13k/2+11 as well. This strictly stronger-than-6.5k order is all that its support argument needs: X<6k/5 follows from 191/30<13/2, the c=0 singleton upper bound is 6.44k+7, the c>0 singleton bound is at most 6.5k+10, and its d=2 co-singleton bound is 6.5k+6. The high-contact, second-cut and degree steps hold unchanged. The two-component theorem only needs k>24.

At six-connectivity every private high A representative touches one anchor, reserving five even slots inside A or S by the boundary of its closed internal neighborhood. Every B contact class therefore has order at most k−5, giving P_B≤6(k−5). Recalling the private-side representative count 6d≤6k−P_B+P_A+6, this sharpens the first window bound to X+Y≤6k+(7/6)X−24. The other window still gives X+Y≤13k−5X. At their intersection the upper bound on total graph order is

    n ≤ (271/37)k−720/37+7 = (271/37)k−461/37.

The large-cycle lower bound is n≥11q+11≥22k/3−88/3. The difference between this lower bound and the two-window upper bound is exactly (k−1873)/111, positive for k≥1874. The other arguments in six-cut-large-degree.md require at most n>7.25k+13 to get X<6k/5, Y>6k, edge codegree at least five, and reject singleton supports on d≥4 residual labels. The same lower bound exceeds it when k≥1874, as do its small-block alternatives. The proof by taking the boundary of the second side then goes through verbatim.
