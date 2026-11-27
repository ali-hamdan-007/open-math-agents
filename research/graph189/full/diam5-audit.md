# Independent audit of the diameter-five degree bounds

The general quadratic bound and the exclusion of minimum degree at most seven are valid at paper level. They use the full positive even-distance cap and the upstream diameter-five endpoint lemma. They do not use 2-connectivity or a traceability criterion. The argument leaves diameter-five graphs with minimum degree at least eight open.

## Layer counts

The upstream `five_endpoints` statement requires only connectivity and the original even-distance cap, and concludes that every distance-five pair contains a vertex below the second-smallest degree \(s\). The order statistic makes this vertex unique. It is the minimum-degree vertex \(z\), whose successive nonempty layers are \(A,B,C,D,F\) of sizes \(a,b,c,d,f\). Any \(A\)-to-\(F\) distance is at least four by the layer indices and is at most four by the endpoint lemma and diameter five. In particular the entire far layer consumes \(f\) even-distance positions at every anchor.

The cap at \(z\) gives \(b+d\le s\), and the allowed neighbors of vertices in \(A,F\) give \(s\le a+b\) and \(s\le d+f-1\). Thus \(a+f\ge s+1\). With \(h=s-f\), \(i=a+b-s\), \(j=d+f-1-s\), and \(g=s-b-d\), we have \(i+d\le a\), \(d\ge h+1\), and \(f\ge b+1\). In particular every vertex of \(A\) misses at most \(i\) vertices of \(B\), and every vertex of \(F\) misses at most \(j\) vertices of \(D\).

If every anchor reached every middle vertex at distance two, then \(c\le h\). No middle vertex can reach all of both end layers at distance two because \(a+f>s\). Thus every middle vertex has at most \(j\) neighbors in \(D\), and degree at most \(b+c-1+j\le b+d-2<s\), impossible. This also rules out a complete \(A\)–\(B\) incidence, so \(i\ge1\) and \(d\le a-1\). A middle vertex missed by some anchor has at most \(i\) neighbors in \(B\), which gives
\[
s+1\le i+c+d,\qquad c\ge (s-a)+g+1.
\]
In particular the middle cannot be visible from every far vertex. A middle vertex missed by a far vertex has at most \(j\) neighbors in \(D\) and degree at most \(b+c-1+j\), giving \(c\ge h+g+2\).

Every \(B\)-vertex has an \(A\)-neighbor and so has at most \(h\) neighbors in \(C\). For a fixed anchor, its visible \(C\)-vertices number at most \(h\), and each invisible \(C\)-vertex has a \(B\)-neighbor missed by the anchor. At most \(i\) missed \(B\)-vertices therefore cover the invisible portion, giving \(c\le h(i+1)\le h(a-h)\). Substitution yields
\[
s\le a-1+\lfloor a^2/4\rfloor.
\]
The floor is legitimate since all counts are integers and \(4h(a-h)\le a^2\).

## Sharpening and the case \(a=6\)

For a missing \(A\)–\(B\) edge, both internal neighborhoods are contained in \((A\cup B)\) minus the two endpoints. They have sizes at least \(s-1\) and \(s-h=f\). Their sum is greater than \(a+b-2\) because \(s>a\) and \(f\ge b+1\). Hence every missing \(A\)–\(B\) edge gives a distance-two witness. Let \(m\) be the minimum number of missed \(B\)-vertices at any anchor. It is positive because an anchor seeing all \(B\) sees all \(C\) at distance two, whereas \(c\ge h+g+2>h\). The cap now gives at most \(h-m\) visible middle vertices at every anchor, and each \(B\)-vertex has at most \(h-m\) neighbors in \(C\). An anchor attaining \(m\) gives
\[
h+g+2\le c\le (m+1)(h-m)\le\lfloor (h+1)^2/4\rfloor.
\]
This forces \(h\ge4\), and \(h\le d-1\le a-2\) then gives \(a\ge6\). Together with \(s+1\le i+c+d\le a+c\), these inequalities yield the stronger handwritten bound \(s\le a-1+\lfloor(a-1)^2/4\rfloor\).

At \(a=6\) the inequalities force \(h=4,d=5,i=1,g=j=0\). Every anchor misses exactly one \(B\)-vertex, so \(m=1\) and the upper and lower bounds force \(c=6\). Each anchor misses at least three of these six middle vertices at distance two, and each such middle vertex has its nonempty \(B\)-neighborhood contained in the singleton consisting of that anchor's missed \(B\)-vertex. The unique missed \(B\)-vertex cannot be the same for all anchors, since every \(B\)-vertex has an \(A\)-neighbor. Two distinct such singletons therefore give disjoint groups of at least three middle vertices, together covering all six. Every middle vertex consequently has exactly one \(B\)-neighbor.

A middle vertex without a \(D\)-neighbor would have degree at most \(1+(c-1)=6<s\). Hence all six middle vertices have a \(D\)-neighbor. Because \(j=0\), every far vertex sees all of \(D\), so each far vertex counts all six middle vertices at distance two and all six anchors at distance four. This forces \(s\ge12\), while \(s\le a+c-1=11\).

## Equality at \(h=4\), and the final case \(a=7\)

The stronger inequality \(h\ge5\) holds at any minimum degree. Suppose \(h=4\). The lower and upper middle bounds force \(c=6,\ g=0,\ m\in\{1,2\}\), with equality in \(c\le(m+1)(h-m)\). For any anchor attaining \(m\), the \(m\) missed \(B\)-vertices have pairwise disjoint \(C\)-neighborhoods of size \(4-m\), and those neighborhoods exactly partition the invisible middle vertices. Indeed the visible part has size at most \(4-m\), the invisible part is covered by those \(m\) neighborhoods, and each neighborhood has size at most \(4-m\). Equality in the sum forces equality in each bound and no overlap with the visible part. Each invisible middle vertex therefore has exactly one \(B\)-neighbor.

Choose one such missed \(B\)-vertex \(b_0\) and an anchor adjacent to it, which exists because \(b_0\) belongs to the second layer. This anchor sees the full block \(N_C(b_0)\) in two steps, so it too attains \(m\) and its visible set is exactly this block. Its invisible set contains the complement, and the same equality argument shows that those vertices each have one \(B\)-neighbor. The block itself already has that property by the first anchor. Hence all \(C\) vertices have only one \(B\)-neighbor. Each needs at least \(s-6>d-5=j\) neighbors in \(D\), since \(s>a\ge d+1\). It follows that all far vertices reach all middle vertices in two steps, contradicting \(c\ge(s-a)+g+1\). This proves \(h\ge5\) in both equality cases, without restricting \(a\).

Now let \(a=7\). Since \(5\le h\le d-1\le a-2\), we have \(h=5,d=6,i=1,g=j=0,m=1\) and \(7\le c\le8\). Each anchor misses exactly one \(B\)-vertex and reaches at most four members of \(C\) in two steps. Thus each \(B\)-vertex missed by an anchor supports at least \(c-4\) middle vertices that have no other \(B\)-neighbor. There are at least two distinct supports, since a common missed \(B\)-vertex would have no anchor neighbor. Because \(j=0\), a middle vertex is at distance two from any far vertex exactly when it has a \(D\)-neighbor. Call such a vertex active. There are at least two active vertices. If there were only one, every length-four anchor-to-far geodesic would pass through that same middle vertex and put all of \(A\cup F\) at distance two from it, contradicting \(a+f>s\).

If \(c=8\), the two disjoint groups of four singly supported middle vertices exhaust \(C\). For \(s\ge9\), a singly supported vertex has at most eight neighbors in \(B\cup C\), so all eight are active. This is impossible because \(c>s-a\). For \(s=8\), each far vertex has only \(s-a=1\) place remaining after its distance-four witnesses in \(A\), whereas the two active vertices already require two places.

If \(c=7\), at least six middle vertices have singleton \(B\)-support, on just two \(B\)-vertices. All six are active, as each otherwise has at most seven neighbors and \(s\ge8\). Therefore \(s-a\ge6\), and \(s\le a+c-1=13\) forces \(s=13\). These six are all the active vertices and exhaust the even-distance allowance at every far vertex together with the seven anchors. Fix any far vertex. Its distance to each \(B\)-vertex is at least three by the layers and at most four by the endpoint lemma. It cannot be four, so each \(B\)-vertex must lie at distance three through an active middle vertex. The layers along a length-three path from \(B\) to \(F\) must be \(B,C,D,F\), so this requires every \(B\)-vertex to be one of the two supports. Yet \(b=s-d=7\). This excludes \(a=7\).

## Strict middle bound at every \(h\)

The equality argument also establishes \(c<(m+1)(h-m)\) for any \(h\). If equality holds, an anchor attaining \(m\) partitions its invisible middle vertices into the disjoint \(C\)-neighborhoods of its missed \(B\)-vertices, each of size \(h-m\). Here \(m\ge1\), and \(h-m>0\) follows from \(c>0\). Pick an anchor adjacent to one of those supports. It sees the entire block of size \(h-m\), so it attains \(m\) and the other middle vertices are invisible to it. They too have singleton \(B\)-support by equality. This would make every middle vertex singly supported.

To rule that out, fix any far vertex \(y\) and put \(K=C\cap N_2(y)\), where \(N_2(y)\) denotes the distance-two layer from \(y\). A \(B\)-vertex with no neighbor in \(K\) cannot be at distance three from \(y\), since a length-three path must traverse the layers \(B,C,D,F\). Its distance is therefore four, using the high-endpoint exclusion of distance five. The vertices in \(A\), in \(K\), and in \(B\setminus N_B(K)\) are disjoint positive even-distance witnesses, so
\[
|N_B(K)| \ge a+b-s+|K| = i+|K| .
\]
Here \(N_B(K)\) is the set of vertices in \(B\) with a neighbor in \(K\). This inequality contradicts singleton \(B\)-support throughout \(K\), because \(i\ge1\). Consequently
\[
c\le\lfloor(h+1)^2/4\rfloor-1,
\qquad
s\le a-2+\lfloor(a-1)^2/4\rfloor .
\]
The strict bound directly rules out \(h=4\), since its upper bound on \(c\) would be five and the lower bound is six. It also rules out \(c=8\) in the \(a=7\) argument, giving a shorter proof of the same exclusion.

## Lean scope and reproduction

I independently copied and compiled `Graph189DistanceLayers.lean`, `Graph189DiameterFiveMidpoint.lean`, and `Graph189DiameterFiveOrder.lean` under pinned Lean 4.33.1 with warnings treated as errors. The printed theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The local incidence lemmas and the arithmetic implication \(4(s+1)\le4a+a^2\) are checked. The sharpened and strict bounds, arbitrary-graph layer setup, and the exclusions at \(a=6,7\) are handwritten. None of the mathematical implications depends on numerical search.
