# A fractional cover of the other side by even-distance sets

Let S be any vertex separator, and A,B distinct components of G−S. For x∈A and any neighbor u of x (including an anchor) put

    J_x(u) = {i∈S : dist(u,i)=dist(x,i)−1}.

Take any nonnegative weights λ_u such that the sum on neighbors whose sets contain i is at least one, for each i∈S. Write e_Y(y) for the count of vertices in Y at positive even distance from y. Under the conjecture's positive-even cap k, the following all-orders inequality holds:

    |B| ≤ e_B(x) + Σ λ_u e_B(u)
         ≤ k−e_(V−B)(x) + Σ λ_u (k−e_(V−B)(u)).

Indeed if a B vertex v is at odd distance from x, choose any i on a shortest x,v path. Each neighbor u with i∈J_x(u) has dist(u,v)=dist(x,v)−1 by the two triangle inequalities. This distance is positive since every candidate u lies outside B. The total weight of such u is at least one, and x itself covers the B vertices at even distance. This establishes both inequalities without any degree or connectivity restriction beyond connectedness for the distances. They hold with A and B interchanged.

For a minimum three-cut, suppose the three anchor pairs are contained in J_x(u_12), J_x(u_13), J_x(u_23), respectively. Assign weight 1/2 to each designated occurrence (combining repeated neighbors). Then |B|≤(5/2)k minus the specified outside budgets. In particular if x is a nonport with all three anchors at distance two, x spends at least three slots outside B, yielding |B|≤(5/2)k−3. If both sides contain such a vertex with the pair-cover property, n≤5k−3, so the moderate-order theorem gives a spanning path whenever k≥16. No assumption about maximum degree or side size is needed. This identifies a structural obstruction in the balanced range: at least one side in a counterexample cannot have this three-pair cover. Other choices of weights yield a direct linear-programming upper bound on the opposite-side order.

The simpler integer version with two neighbors is the three-even-set argument in global/cut3/shallow-three-cut.md. Weighted capacities retain the already-used slots on the source side.
