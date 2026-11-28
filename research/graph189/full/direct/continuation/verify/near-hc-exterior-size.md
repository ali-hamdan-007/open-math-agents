# Additional lower bounds on the size of a near-Hamilton-connected exterior

Use the hypotheses of sep/cover/local-cover-contacts.md. Put m=|C|, let j≥2 be the maximum matching of exterior contacts, and set r=m−1+j−k. That paper gives 3j<k and r≥2. The following refinement holds:

    2r≥j+2,     r(2k−5j)≥(j+1)(k−2j)−j+1.

In particular m≥k−floor(j/2)+2. All statements allow a unique low vertex of arbitrary degree and a mixed minimum contact cover.

Write M for the path marks and Y for the C vertices of a minimum cover, with |Y|=u and |M|=j−u. If the low vertex lies in C−Y and has a neighbor in C−Y, choose one such neighbor as c. Otherwise choose any high c∈C−Y. Existence follows from m−1>j. Let b count the other C members nonadjacent to c, and let z count the marks in M missed by c. Then d(c)=k+r−u−b−z and b+z≤r−u. Each high vertex in C−Y nonadjacent to c has at least j−r+1 neighbors in M, since it loses at least one of its m−1 possible internal neighbors. This additional one for a nonneighbor is the interval reviewer’s refinement.

Suppose z<j−r+1. Each high C nonneighbor of c outside Y shares a c-mark, since its at least j−r+1 real contacts cannot all lie among the z missed ones. We can cover the entire distance-two layer of c by at most j actual neighbors of c. Start with its neighboring M marks and its neighboring Y vertices. For any missed M mark or missed Y vertex at distance two choose a neighbor of c witnessing that distance, using at most one place for each member of M∪Y overall. Every high internal nonneighbor outside Y is already covered by a shared mark. If there is a low vertex in C−Y, it is adjacent to c by choice whenever it has a C−Y neighbor. Otherwise such a low vertex has neighbors only in Y∪M, so if it is at distance two it is also covered by one of the initially chosen neighbors. For a distance-two vertex outside C∪M∪Y, a route that starts via an M or Y neighbor is already covered. Any route starting through a C−Y neighbor cannot leave C except at M. This proves the cover assertion.

The local order upper bound is consequently 1+d(c)+k+j(k+1−j). The matched-gap and endpoint lower bound from the cited paper is m+j(m−ε)+j+k+1−u−z, with ε∈{0,1}. Subtraction gives 1+j(r−ε)+b>0. Thus z≥j−r+1, and hence b≤2r−j−u−1. For the same c, the general distance-two cover using at most j+b slots gives the necessary inequality b(k−2j)≥1+j(r−ε). In particular b≥1. It follows that 2r≥j+2 and (2r−j−1)(k−2j)≥1+j(r−1), yielding the displayed statements.
