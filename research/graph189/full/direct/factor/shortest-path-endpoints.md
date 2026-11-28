# Exterior shifts at endpoints of the shortest member of a minimum path cover

Retain the assumptions of minimum-path-cover.md. Every singleton member x in any minimum path cover satisfies 2deg(x)≤k. Indeed its neighbors on other paths avoid endpoints and consecutive positions. They also avoid positions two apart: replacing the midpoint by x gives a minimum cover whose singleton midpoint must be low; x is already the unique low vertex. Thus all shifted neighbors of x are distinct distance-two witnesses. Consequently if 2δ>k no minimum cover has a singleton. At k=5 the triangle configuration in minimum-path-cover.md is impossible as well, because its required singleton exchange would violate this bound.

No three-vertex piece inducing a path x–q–y is possible. Choose x high, possible as the two endpoints are distinct. The exterior contacts A(x) avoid exterior endpoints; if two contacts were consecutive, inserting x alone between them would leave qy as a two-vertex piece in a new minimum cover, contrary to the two-vertex exclusion. Thus all |A(x)|+r_x shifts are distance two from x; y is a further such vertex. Since |A(x)|=deg(x)−1≥k−1 and r_x≥1 this is impossible. Together with the triangle result this excludes all three-vertex members of minimum covers whenever k≥5.

Choose, over all minimum covers, one with a member Q of the smallest achievable order m. Write A(v)=N(v)∖Q for v∈Q, and H(A) for the union of ±1 shifts on the remaining oriented paths. Assume there is more than one piece. Every exterior endpoint misses Q, because joining its path to a terminal segment of Q via a contact leaves a shorter complementary segment or reduces the total number of paths. Hence for every v, |H(A(v))|=|A(v)|+r_v, where r_v counts the step-two runs and may be zero.

If x is an endpoint of a spanning path of G[Q], H(A(x)) is anticomplete to Q. Indeed if a∈A(x) is consecutive to b in an exterior path and b has neighbor q∈Q, use the initial segment from x to q of a spanning Q-path to replace the ab edge. This either eliminates Q or leaves one shorter complementary terminal segment. In particular H(A(x)) is disjoint from A(x). As A(q)∖A(x) for q∈N_Q(x) also sits at distance two, is disjoint from H(A(x)), and is exterior, the following holds for every high feasible endpoint x:

    |N₂(x)∩Q| + |{v:d(v,x) even and ≥4}| + r_x
       + |(⋃_{q∈N_Q(x)}A(q))∖A(x)| ≤ deg_Q(x).

The ≥4 term here requires the full even-distance cap; delete that term when only the distance-two bound is assumed.

Assume m≥2, equivalently no minimum cover has a singleton. For any endpoints x,y of the same spanning path of G[Q], a contact in A(x)∩A(y) can occur only in singleton runs of A(x) and A(y). In a nonsingleton run, it and the neighboring contact two steps away would allow replacing their midpoint by the full spanning Q-path, leaving a singleton in a minimum cover. Thus |A(x)∩A(y)|≤min(r_x,r_y).

If Q has a spanning cycle, take two consecutive high vertices x,y on it (a genuine cycle has such an edge). They are compatible endpoints and adjacent. From x, the external sets H(A(x)) and A(y)∖A(x) are disjoint distance-two witnesses. Hence

    k ≥ |A(x)|+r_x+|A(y)|−|A(x)∩A(y)| ≥ |A(x)|+|A(y)|.

Both exterior degrees are at least k−m+1. Thus m≥ceil(k/2)+1.

If Q is non-Hamiltonian and x,y are compatible high endpoints with a common neighbor w∈Q, then m≥ceil(2k/3)+1. First deg_Q(x)+deg_Q(y)≤m−1: for the ordered spanning path from x to y, the predecessor shifts of the internal neighbors of x cannot intersect the neighbors of y in the manner that would close a spanning cycle (equivalently, use the usual Ore endpoint wrapping lemma). Moreover H(A(w)) is disjoint from A(x)∪A(y) since H(A(x)) and H(A(y)) are anticomplete to Q. From w, (H(A(w))∪A(x)∪A(y))∖A(w) gives distance-two witnesses; its size is at least |A(x)∪A(y)|+r_w. Thus |A(x)∩A(y)|≥|A(x)|+|A(y)|−k≥k−m+1. Also r_x≤deg_Q(x), r_y≤deg_Q(y) by the endpoint inequality. Consequently m−1≥deg_Q(x)+deg_Q(y)≥2(k−m+1), as required. The result applies in particular at 2δ>k whenever the described Q and endpoints exist.
