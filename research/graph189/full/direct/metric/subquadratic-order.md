# An unrestricted subquadratic order bound

Let G be a finite connected graph, and let k≥1 be its second-smallest degree. Suppose each vertex has at most k other vertices at even distance. Choose a minimum-degree vertex z, so every other vertex has degree at least k. Denote its first three layers by A,B,C, with sizes a,b,c. The argument bounding c only needs the bound k on vertices at distance exactly two. If c>0, define h as the maximum, over anchors x∈A, of the number of C vertices at distance two from x. Then 1≤h≤k and the following bounds hold simultaneously:
$$
 c\le h(k-h+1),\qquad c(k-h+1)\le ah+b(k+h).
$$
In particular
$$
 c^2\le h(ah+b(k+h))\le 3k^3, \qquad
 |V(G)|\le 1+3k+\lfloor\sqrt{3k^3}\rfloor.
$$

Assign each vertex of C to one of its B-neighbors, and write f(y) for the number assigned to y∈B, so Σf=c. For every x∈A, all the vertices assigned to B-neighbors of x are at distance two from x. Their total number is at most h.

Fix an x∈A attaining h. The columns y∈B not neighboring x have total assigned mass at least c−h. Assign each such positive column to an arbitrary anchor x'∈A adjacent to it. The total mass received by any x' is at most h, by the preceding observation. If p anchors receive any mass, then c−h≤ph. Choose one of its assigned columns for each receiving anchor. Each such anchor x' differs from x, since its chosen column is nonadjacent to x. If x' is nonadjacent to x, it is a distance-two witness from x via z. If x' is adjacent to x, its chosen column is a distance-two witness from x via x'. These p witnesses are distinct: those in A are distinct anchors, and those in B were assigned to different anchors. None lies in C. Since x already has h distance-two vertices in C, p≤k−h. This proves c≤h(k−h+1).

For y∈B put g(y)=|N(y)∩C| and d_S(y)=|N(y)∩S| for S=A,B. Every neighbor in C of y is at distance two from any A-neighbor of y, so g(y)≤h. The neighbors of y can only be in A,B,C, and d(y)≥k, whence d_A(y)+d_B(y)≥k−h. Summing with weights f(y) gives
$$
 c(k-h)\le \sum_{y\in B}f(y)(d_A(y)+d_B(y)).
$$
The anchor contribution is at most ah by the assignment inequality. For each y∈B, the C vertices assigned either to y or to one of its B-neighbors lie at distance one or two from y. Their total number is at most g(y)+k≤h+k. The assignment partitions C, so the sum of the loads on the B-neighbors of y is at most h+k−f(y). Summing over y gives a B contribution at most b(h+k)−c. Combining yields the second bound. Multiplying c≤h(k−h+1) by c and then applying the second bound proves the quadratic inequality for c. The final numerical estimate uses a,b,h≤k.

For the order conclusion, the existing upstream Graph 189 reduction proves diameter≤5 and that every distance-five pair includes a vertex below k (diameter_le_five and five_endpoints). The second and fourth layers together contain at most k vertices by the original positive-even cap. All fifth-layer vertices are at distance four from every first-layer vertex: their separation is at least four by the distance from z, at most five, and both have degree at least k so it cannot equal five. Thus the fifth layer has size at most k. Summing all layers gives the stated order bound. If c=0, higher layers are empty, and n≤1+2k already.

This proves a subquadratic bound for arbitrary degrees. It does not prove n≤4k+3, and supplies no example above that proposed line.
