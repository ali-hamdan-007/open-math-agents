# A contact count from both ends of a separator

In a qualifying counterexample let P be a longest path. Let C be an omitted component of size m containing a vertex c of degree at least k. Suppose all C-to-P edges meet a set S of a distinct marks on P. Suppose in every realizable ordering of V(P) as a path, the marks delimit a+1 gaps (including tails) of at least L vertices apiece. In particular one may take L=m when C is Hamilton-connected and an a-matching joins C to all of S. Put r=a−|N(c)∩S|, the number of marks missed by c. If at least k+1 high endpoints are attainable among these realizations, then

    |P| ≥ aL+a+k+1−r.

Indeed writing σ=|P|−a−(a+1)L for the surplus, any attainable endpoint e has at most L−1+σ neighbors outside S, all on P. In any piece following a mark, a neighbor among its first L vertices would rotate the preceding mark to a position ≤L, which is forbidden. The initial piece contributes at most its length minus one. Consequently every high attainable endpoint has ≥k−L+1−σ neighbors in S. If this exceeded r, all k+1 high attainable endpoints would have a common adjacent mark with c and would lie at distance two from it (as endpoints cannot touch an omitted vertex). Counting these vertices violates the positive-even cap k at c. Rearranging the resulting σ≥k−L+1−r proves the displayed inequality.

In particular at L=m, any such c misses at most a+m−1−k marks by its degree. Therefore n≥|P|+m≥am+2k+2, irrespective of the low vertex's degree. This is the quantitative form used to finish the odd (one below half) case in ../sep/k10/odd-larger-exterior.md. It also measures how much surplus has to be paid when an omitted component is routed with a prescribed set of marks in the general problem.
