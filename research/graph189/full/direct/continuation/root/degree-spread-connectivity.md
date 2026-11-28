# Traceability with connectivity above twice the degree spread

Write k for the second-smallest degree and r=Δ−δ for the difference between the largest and smallest degrees. Under the Graph 189 hypotheses, κ≥2r+2 and k≥2(r+3)² suffice for a Hamiltonian path. For r=0 the unrestricted regular case is previously settled. Assume r≥1.

The [wedge order theorem](../verify/wedge-order-and-hamiltonicity.md) gives a Hamiltonian cycle when n>(r+3)k+1, so suppose n≤(r+3)k+1. Assume there is no spanning path. Exactly as in the proof for [connectivity three](moderate-order.md), take an omitted high-bearing component of a longest path, and take its whole vertex set if it is 2-connected or a good endblock otherwise. Write b for the order, h=ceil(k/2). Then b≥h+1, and if b≤k−2 the contact matching gives n≥b(k−b+3)−1.

In fact b≥k−r. If b≤k−r−1 then b≤k−2. At the smaller endpoint h+1 the concave quadratic b(k−b+3)−1 is at least (k/2+1)(k/2+1)−1, exceeding (r+3)k+1 under the hypothesis. At k−r−1 it is (k−r−1)(r+4)−1, also above (r+3)k+1 since k>(r+1)(r+4)+2. This contradiction gives b≥k−r. Fan's circumference theorem gives a disjoint cycle of length d≥min(b,2h)≥k−r.

Use l=2r+2 distinct cycle-to-path connectors, which exist by the connectivity assumption and Menger's theorem: the path has at least k+1 vertices, and k−r≥l. The two tails and l−1 gaps give

    n ≥ 3d+l+(l−1)(ceil(d/2)+1)
      ≥ (r+7/2)(k−r)+4r+3
      = (r+3)k+1 + k/2−r²+r/2+2 > (r+3)k+1.

This contradiction proves the claim. The same proof applies with any positive integer r bounding the maximum local excess d(w)+e(w)−d(u)−d(v) over induced paths u,w,v, where e(w) is the number of other vertices at even distance from w. The global degree spread is a convenient sufficient bound.
