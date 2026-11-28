# Diameter five bounds from both ends of the geodesics

Let a connected qualifying graph have diameter five. Write s for its second-smallest degree. Use the established fact that every distance-five pair contains its unique below-s vertex z, and write A,B,C,D,F for its successive distance layers. Lowercase letters denote their sizes, so a=deg(z). Put

    h=s−f,   l=s−a,   i=a+b−s,   j=d+f−1−s,   g=s−b−d.

Thus b=i+l, d=h+1+j, a=i+d+g. Write m for the minimum number of omitted B vertices among the A-neighborhoods. Previously established facts used here are i,m≥1, g,j≥0, each A-to-F distance is four, all missed A-to-B adjacencies have distance two, and each C vertex that is a midpoint of an A-to-F geodesic is within distance two of either all A (type L) or all F (type H). Both alternatives cannot hold at one vertex since a+f>s. The sets A,F are nonempty, so there is at least one midpoint. Let D+ consist of D vertices having a neighbor in F. A middle vertex is a geodesic midpoint precisely when it has a D+ neighbor, since every C vertex has a B-neighbor and every B vertex has an A-neighbor.

## Counting the remote endpoint contacts of both intermediate layers

A vertex in B has at most h−m neighbors in C: any incident anchor sees these at distance two, all f far vertices at distance four, and at least m nonadjacent B vertices at distance two. The B vertex therefore has at least

    s−(b−1)−(h−m)=j+g+m+2

neighbors in A. In particular each C vertex lies within distance two of at least j+g+m+2 anchors. Each anchor sees at most h−m vertices of C. Double counting gives

    c(j+g+m+2) ≤ a(h−m).                                      (1)

The previously proved strict cover estimate c<(m+1)(h−m) yields

    c/(h−m) < sqrt(a).

Indeed the square is less than (m+1)a/(m+2)<a. The earlier s≤a−1+c and h≤a−2 imply s<a−1+(a−3)sqrt(a). This improves the quadratic dependence to order a^(3/2).

Every D+ vertex has at most l neighbors in C because any far neighbor sees all a anchors at distance four. Consequently it has at least

    s−(d−1)−l=i+g+1

neighbors in F. A type L middle vertex is at distance two from all A and thus at most l vertices of F. Using any of its D+ neighbors gives i+g+1≤l whenever an L exists. Likewise a type H middle vertex sees at most h anchors; using any B-neighbor gives j+g+m+2≤h whenever an H exists.

In fact l≥2 always. If l=1, each far vertex y can see just one midpoint at distance two, and must see one because every A-to-y distance is four. This unique midpoint must serve every anchor, making it type L, which requires l≥i+g+1≥2. As a consequence every graph in the remaining high-order range n>3s+2 has h≥6. Indeed the formerly possible h=5 has c≤floor((h+1)^2/4)−1=8, whereas the order identity n=2s+1+a+c−h−g and l≥2 imply c≥h+l+g+2≥9.

## A linear bound in the two end allowances

If both types of midpoint occur, the preceding inequalities and the order identities give

    a = i+h+1+j+g ≤ 2h+l−g−m−2.

Suppose all geodesic midpoints are type H. Fix any y∈F and let K be its distance-two set in C. A vertex of B not adjacent to K cannot reach y in three steps; it is at distance four, using the high-endpoint property. Since y already has all A and all K as even-distance witnesses, at least b−(l−|K|)=i+|K| vertices of B have a neighbor in K. Each of these B vertices has at most h anchor-neighbors: its chosen H neighbor in K already sees all F at distance two and has room for at most h anchors. On the other hand each anchor can miss at most h−1 B vertices: it sees every F and at least one middle vertex at distance two. Counting missed A–B adjacencies therefore gives

    (i+1)(a−h) ≤ a(h−1).

If a>2h, this forces i<2h. Together with j+g+m+2≤h one obtains a<4h. If a≤2h the latter bound also holds.

Suppose instead all geodesic midpoints are type L. Put t=|D+|. Every D+ vertex has some C-neighbor by its distance layer, and that C-neighbor is a geodesic midpoint. Since it is type L, at most l far vertices can neighbor the D+ vertex. Its number of C-neighbors is also at most l, as shown above, so its degree inside D is at least s−2l=a−l. For any incident far vertex y, at most l of those neighbors fail adjacency to y: each such neighbor is at distance two from y and y already sees all a anchors at distance four. Thus t≥a−2l.

All nonadjacent pairs with one vertex y∈F and another w∈D+ have a common neighbor inside D∪F. Indeed their degrees inside this union are at least s and s−l=a, respectively, whereas s+a>d+f−2 since a≥d+1 and s≥f. This forces a common internal neighbor when y,w are nonadjacent. Consequently each far vertex misses at most l of D+, while each vertex of D+ has at most l far neighbors. Double counting their edges gives

    f(t−l) ≤ tl,    t≥a−2l.

If t≤2l then a≤4l. If t>2l then f<2l, so a=f+h−l<h+l. Combining all three midpoint patterns proves

    a ≤ 4 max(h,l),    s ≤ 5 max(h,l).                        (2)

For a putative diameter-five counterexample, n>3s+2. Hence c≥h+l+g+2 and the known c≤floor((h+1)^2/4)−1 yield

    2 ≤ l ≤ floor((h+1)^2/4)−h−g−3.

Together with (2) this bounds a and s in terms of the far allowance h alone. The order identity and the bound on c then bound n as well. For each fixed value of h, only finitely many diameter-five graphs need be considered for the conjecture. No assertion of traceability for all diameter-five graphs is made here.
