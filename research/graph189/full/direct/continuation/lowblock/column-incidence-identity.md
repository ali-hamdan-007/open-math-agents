# A maximum-degree root pays all third-layer widths in its first-layer even budgets

Let x have maximum degree Δ≥k. Let A be its neighbor set, B its distance-two vertices, and C any set of its distance-three vertices. Suppose each vertex has at most k other vertices at even distance. Write W(y) for the number of A vertices at distance two from y plus the number of B neighbors of y. Then

    ∑_{y∈C} W(y) + (Δ−k)|B| + ∑_{a∈A}(Δ−d(a)) ≤ kΔ.

In particular every lower bound w on the individual W(y) gives w|C|≤kΔ. This version does not use the second-minimum degree condition, the diameter, any information about the low vertex, or any lower order threshold.

At each a∈A put p_a=|N(a)∩B|. Its closed neighborhood within A has d(a)−p_a members: of its neighbors outside A one is x and the rest belong to B. Hence exactly Δ−d(a)+p_a members of A are at distance two from a. Together with the B and C members at distance two, these are disjoint uses of its k slots. In particular the p_a direct neighbors in B can be charged to this row's A uses, leaving an additional Δ−d(a) slots already spent.

At each b∈B choose any u∈A∩N(b). All C neighbors of b have distance two to u, as do all members of A outside the closed A-neighborhood of u. Those groups are disjoint, so b has at most |N_A[u]|−(Δ−k) neighbors in C. Every point of N_A[u] has distance one or two from b. Consequently the C neighbors of b, together with Δ−k extra units, cost at most the number of A points at distance at most two from b. On summing over b, the distance-one pairs are already paid by the direct-neighbor replacements in the preceding paragraph. The distance-two pairs and the remaining A–C pairs are paid directly in the corresponding A rows. Summing their k budgets proves the inequality.
