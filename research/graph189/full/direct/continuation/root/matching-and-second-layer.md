# When shared path contacts cover a second layer

Let P be a longest path in a hypothetical Graph 189 counterexample and C a connected high-bearing exterior component of size m. Suppose its contact matching into P has size j≤(k+1)/2 and that any prescribed distinct matching terminals in C can be joined through at least m−1 vertices of C, with each matched terminal also starting such a path. These hypotheses hold in the near-Hamilton-connected case. Write M⊆P and Y⊆C for any minimum vertex cover of the contact edges, p=|M|, u=|Y|, p+u=j, and W=C−Y. Suppose W contains a high vertex. Then
```
2(k−m+1) ≤ p,       so m ≥ k+1−floor(p/2).
```
Thus the omitted component must be nearly of size k if there are few path marks. This condition concerns any minimum cover, including one which contains vertices from inside C.

Put r=m−1+j−k. Every high member of W has at least k−m+1=j−r neighbors in M, since it has no path contacts outside M. Assume twice that number exceeds p. The high members of W then all pairwise share a mark. If a low z lies in W and has a W neighbor, choose such a neighbor c; otherwise take any high c in W. Let t be its number of marked neighbors. We exhibit a cover of the vertices at distance two from c using at most j of its neighbors.

First include all t adjacent real marks and one predecessor for each real mark missed by c that lies at distance two. These cost at most p. Next, for each point y in Y, include y if it neighbors c, or one predecessor if it is at distance two from c. This costs at most u. Any distance-two vertex on P or in a different exterior component is reached through a neighbor on P, through Y, or is itself a contact mark of some W member (and so lies in M). Every distance-two high member of W shares a mark with c. The low vertex of W, if any, either neighbors the chosen c already, or has no W neighbor at all; in the latter case a path of length two from c to it goes through Y or through one of c's neighboring marks. Thus every required vertex is covered.

Take an inclusion-minimal subcover of size q≤j. The rooted order bound from ../sep/cover/local-cover-contacts.md gives n≤1+d(c)+k+q(k+1−q)≤1+d(c)+k+j(k+1−j). Write e=d(c)−k. Every size-j matching uses each cover member once and never has an edge between cover members: its j disjoint edges need at least j different cover vertices. In particular its real marks include all M, and c touches t of its j path labels, missing at most j−t. Its internal degree is at most m−1, giving e+(j−t)≤r. The gap bound from marks-and-endpoints.md at L=m−1 gives
```
n ≥ m+j(m−1)+j+k+1−(j−t).
```
Subtracting the upper bound, this is a contradiction whenever 1+j(r−1)>0. This applies to every r≥1. If r=0 all j labels are real path marks and all highs in C are universal in C and touch all j. In particular C is a clique and L=m is available. The extra j in the lower bound gives a strict contradiction here too. Negative r is excluded by the existence of a high member of W. The asserted inequality follows.

The pairwise-intersection step can also be used when the bare cardinality bound fails: it suffices that an eligible high c shares a real mark with each high nonneighbor in W. The previous proof then still supplies a cover of size at most j and rules out that contact pattern.
