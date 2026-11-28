# A two-unit saving per remote penultimate vertex

Let G satisfy the Graph 189 hypotheses, write k for its second-smallest degree, and assume k≥3. For an induced path u,w,v write j=|N(u)∪N(w)∪N(v)|−d(u)−d(v), and let e(w) be the number of other vertices at even distance from w. Then

    (k−1)j ≤ 3k+2−n+(k−2)(1+d(w)+e(w)−d(u)−d(v)).

In particular a wedge of positive defect forces n≤3k+1+(k−2)(d(w)+e(w)−d(u)−d(v)). If the anchored excess in parentheses is bounded by r on every induced wedge with endpoints different from a prescribed z, then n>3k+1+(k−2)r gives a spanning path starting at z. With z of minimum degree one may take r=Δ−k, independent of any exceptional low degree.

Here are the additional overlap and distance arguments beyond the general [wedge inequality](wedge-order-and-hamiltonicity.md). Let Q=N(w) outside N(u)∪N(v), C=N(u)∩N(v) and C₁=C∩N(w). We have |Q|−|C|=j and |C₁|≤|C|−1. All of Q occur in the closed even sets of both u and v. The complement of the union of the three closed even sets consists of C₁ and the vertices T at a common odd distance ≥3 from the three roots.

Choose for every t∈T a penultimate vertex a on a shortest w-to-t path. The used penultimates at distance two from w are in M=N₂(w) outside N(u)∪N(v). For each such a let b be a fixed predecessor on a w-to-a geodesic and c_a the number of endpoints u,v adjacent to b. The predecessor differs from u,v since a avoids both neighborhoods. Every target assigned to a is at distance exactly two from b, as are any of u,v not adjacent to b, via w. These sets are disjoint. At most k−2+c_a targets can therefore be assigned to a. Also a itself lies in the closed even set of w and those of the c_a endpoints adjacent to b. These are c_a further duplicate incidences beyond the already counted duplicates in Q, since Q⊆N(w) and a is at distance two from w.

Every target at common odd distance at least five has degree less than k. Indeed at least one of the three roots has degree ≥k, and any pair of high vertices has distance at most four by the established original-hypotheses diameter theorem. There is at most one such target. Every used penultimate beyond distance two consequently receives at most one target, which is at most k−2.

The candidate penultimates number at most K=|M|+e(w)−|N₂(w)|=1+d(w)+e(w)−d(u)−d(v)−j. If c is the sum of all c_a on used distance-two penultimates, then |T|≤(k−2)K+c. The union of the three closed even sets has size ≤3(k+1)−|Q|−c, so |T|≥n−3k−2+j+c. Comparing proves the inequality. The rooted local Ore theorem gives the spanning-path consequence.

If every common-odd target ≥5 is absent the same proof holds for arbitrary finite connected graphs with an even-distance cap. In particular it applies under a graph diameter bound of four without any degree hypotheses.
