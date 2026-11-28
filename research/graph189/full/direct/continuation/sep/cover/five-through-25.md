# Connectivity at least five through second-smallest degree 25

Every finite connected Graph 189 graph with connectivity at least five and second-smallest degree k≤25 is traceable. The theorem is already known at k≤18. We give the common argument for 19≤k≤25. In the remaining cases use the lower connectivity s=5 throughout, and let U=2k+1+floor(sqrt(k²(k+1)+1)). The verification uses elementary integer arithmetic in five_blocks.py, with 116 parameter tuples, without a graph search or a satisfiability solver.

First, any near-Hamilton-connected exterior as in k14-k15.md has matching number j≥5 and order m≥k−floor(j/2)+2 by ../../verify/near-hc-exterior-size.md. Also 3j<k. Over these integers (j+2)(k−floor(j/2)+2)+j−1>U at each of the seven degrees. This excludes the near case.

For a small endblock write b for its order, J for the contact matching of its all-high noncuts, and h=ceil(k/2). We have b≥h+1, J≥max(4,k−b+1) and n≥(J+2)b+3h−1. Checking these integers against U leaves only J=4 and b=k−3 or k−2. At b=k−3 each noncut requires all four matched marks and all other B members, including articulation w. The noncuts constitute a clique complete to a five-member boundary, of degree k. At b=k−2 the noncuts need at least three marks. If an interior cover uses one noncut u and three marks, the remaining noncuts again form a clique complete to the five-member boundary of three marks, u and w. For a pure cover of four marks, each noncut misses at most one among the other noncuts and five boundary vertices. A noncut missing any boundary vertex is internally universal and has a second-layer cover of five, by adding at most one witness for its missed boundary member. If all meet the boundary then their internal nonneighbors are already covered by any boundary vertex. Thus the local root bound in all cases gives n≤1+(k+1)+k+5(k−4)=7k−18, contradicting the endblock lower bound, whose minimum among the surviving b is 6(k−3)+3h−1>7k−18 at k≤25 and h≥k/2. The case k=19 has no surviving small-endblock tuple.

## The large-block calculation

Use the notation H=N_C[x], R, r, H*, I, q, l, J of k14-k15.md. Recall |H*|=q+1−l. The large-cycle bound is n≥(s+5)q+2s−1 in a whole and an extra h−3 in an endblock. A one-member gateway inside C is impossible, and 2≤r≤2q−k+1, with l=1 possible only at r≤2q−k. The lower good-block order b≥2q−1 guarantees I is nonempty whenever q−r−3>0, checked in all seven ranges. Therefore b≥2q+2 by the q good-block neighbors of a member of I outside H. In a whole improve the large-cycle bound by two, and the exterior contribution is at least m₀=2q+2 in a whole and 2q+2+h in an endblock.

Put d₀=k−q−l, a lower bound on the degree in H* of every member. The universal x guarantees a route of at least d₀+1 vertices through H* between any two prescribed H* terminals. When 2d₀≥|H*|+1 we can take |H*| vertices by Hamilton-connectedness. The same length is valid when l=1, |H*|=2d₀ and d₀≥3. In this last case all high vertices of the full H have degree at least d₀+1 in H. If the low has at least three H-neighbors, H is Hamilton-connected by the standard single-exception terminal closure lemma. If it has at most two H-neighbors, one is universal x, so after its deletion at most one high member besides x drops below d₀+1, and that member still has degree at least three. Thus in this case H* is Hamilton-connected. The terminal lemma applies whenever all but one vertices have degree at least ceil((N+1)/2) on N vertices and the exception has degree at least three: the high vertices close to a clique after adjoining the degree-two terminal marker; the possible low then has a neighbor outside the prescribed terminal pair. Equivalently the original graph is automatically 2-connected under these degrees. In the alternative using full H, take the tail connector from its last H vertex before I, so it is disjoint from the chosen H traversal. Denote the available length by L.

Every H* member has at least k−q−r path contacts and x needs at least k−q, hence J≥k−q−r+1 in these ranges. Put d=1 when l=1 or when the whole case has r=2q−k+1, and zero otherwise. The original direct contact count n≥m₀+J+(J+1)L+2(q−r+1+d) now excludes oversized J. Its tail correction follows from the connected good block after deletion of the prescribed terminal and the minimum I-degree q−r−1, improved to q−r when there is no exceptional member outside H∪R.

Choose a minimum H*-contact cover of size J, with p marks, u=J−p members of H*, and w=|H*|−u uncovered high members W. There are at least k−q−r real marks, since W is nonempty in every residual tuple. If p<k−q, x must belong to the cover. Each W member misses at most a=q+r+p−k edges among its other H∪R members and these p marks. The potential additions to H* are the r members of R and, when l=1, the deleted low in H. There are r+l potential additions. Ordered by nonincreasing number of W neighbors, addition i (numbered from zero) is guaranteed at least

    max(0,w−floor(wa/(r+l−i)))

W neighbors, since all r+l−i additions from its rank onward miss at least as many edges into W. Any addition with at least two W neighbors belongs to the good block: outside an endblock it could have at most its one articulation as neighbor in that block.

For g=0,…,r+l consider K=H* together with the g best additions, using only additions with at least two certified W neighbors. Its order is N=|H*|+g. Each W member has degree at least N−1−a in K. A covered x has degree at least |H*|−1, other covered members have degree at least d₀, and the additions have the preceding ordered lower bounds. Either of the following certifies K is Hamilton-connected:

- All degrees are at least three and all but at most one are at least ceil((N+1)/2).
- N≥2a+3, 2w≥N+1, and every member outside W has degree at least a+2. In the terminal-marker closure at threshold N+1, missing W-to-W edges first close, and every missing edge from W to outside W can be added by degree sum (N−1−a)+(a+2). W is now universal, and the remaining edges close by 2w≥N+1.

The J direct contacts from H* remain. Every direct K-tail can continue via the connected good block into I, gaining at least A=q−r+d, with another vertex when g=0 from the H-to-I intermediary. Hence n≥m₀+J+(J+1)N+2A. Independently, s disjoint connectors from K to P give n≥m₀+s+(s+1)N+min(4,2+A,2A). Two units of connector interior yield at least four additional vertices; one unit leaves at least one outer connector direct and its tail can continue; no intermediaries means both outer tails extend. These connectors are available since N≥s in the residual cases.

For each tuple the following margin is the maximum proved order excess over U among these choices of g and the two counting rules, followed by the minimum over all tuples for that k. The signed complete rows are saved in five_final.log.

| k | U | Residual tuples | Minimum excess |
|---|---:|---:|---:|
| 19 | 123 | 1 | 18 |
| 20 | 132 | 5 | 11 |
| 21 | 141 | 14 | 10 |
| 22 | 150 | 3 | 15 |
| 23 | 159 | 13 | 6 |
| 24 | 169 | 35 | 4 |
| 25 | 178 | 45 | 3 |

The generator uses no branching on individual graph edges or unknown populations. Running python five_blocks.py 19 25 reproduces the table's 116 six-parameter rows (whole/endblock, q, r, l, J, p), each with its matching upper and lower order. All lower bounds exceed U. Thus the two alternatives to the near-Hamilton-connected case are impossible as well.
