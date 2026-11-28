# Six-connectivity at sufficiently large second-smallest degree

Every qualifying graph of vertex-connectivity six and second-smallest degree k≥100000000 is traceable, independently of maximum degree, order, and placement of the possible low vertex.

Suppose otherwise. Set s=6. The optimized good-block and connector bounds used in private-five-cut.md give n≥11q+11>(22/3)k−(22/3)sqrt(3k)−8 in the large-block case. In the small-block case the whole-component endpoint of the concave order bound is 8k−35, and the terminal linear endpoint is 7(k−4)+3ceil(k/2)−1; the alternate quadratic endpoints are larger. Thus in either case

    n > (6+49/37)k + 50.

Indeed 22/3−(6+49/37)=1/111, and k/111−(22/3)sqrt(3k)−58>0 throughout this range. Fix any minimum six-cut. Its complement has exactly two components. Write A for the smaller high side and X≤Y for the respective high populations. Since XY≤kX+6k², X/k≤3, and the convex function x+1+6/x on [6/5,3] has maximum 36/5, the order bound gives X<6k/5 and Y>6k.

Each label has a high A contact. If A is the single low vertex it touches all six, and it and the six anchor quotas cover all B vertices, giving n≤7k+7. Otherwise some A contact is high (a sole low vertex cannot be the only attachment for a nonsingleton component). A label with only the low A contact z supplies an edge whose common neighbors all lie among the other anchors. The edge-order bound gives at least ceil((n−3k−2)/(k+1))≥5 such neighbors, so this label touches all the others. At |B|>6k no first step from A reduces two anchor distances by the parity cover. Thus any high port at a different label must also touch this label, contradiction.

## Private high ports are excluded

Suppose all high A ports have single support. Every label has a high private representative, so summing their high internal-neighborhood lower bounds and their EVEN B-port/nonport counts as in private-five-cut.md gives Y≤6k+P_A/6+1, allowing arbitrary low A contacts. A high A nonport implies this all-private case: such a vertex must have depth two (depth three would see all Y high vertices at distance four); its nearest labels require at least six covering A ports since otherwise it and five ports cover all of B. Thus every label is nearest and no A port can touch two labels.

For the second bound in the private case choose high A representatives at the six labels. If no high B nonport has all six labels nearest, these six roots cover every high B vertex at even distance, contradicting Y>6k. Fix such a nonport y_B, and let W_B consist of the high vertices of its internal closed neighborhood in B, of size at least k. At each label choose a B representative adjacent to y_B, so every W_B vertex lies at distance at most two from this representative. Let W_A be all X high A vertices with the already chosen high representatives. Each pair of high A vertices has distance at most two: each has internal degree ≥k−6, and |A|≤X+1<6k/5+1 implies that nonadjacent pairs have a common internal neighbor. Every high B nonport has depth exactly two. Indeed if a high B vertex had depth three, the existence of a high A nonport is already inconsistent with the high-pair diameter; if every high A member is a private port, it sees all X high members of A at distance four, forcing X≤k−6 although such an A member has degree at most X+1.

For either side T with high window of order w_T, and label i with window contact count p'_Ti and whole-side high contact count p_Ti, at least w_T−p'_Ti−k+p_(T',i) of its high window members are at distance two from i. Indeed the representative sees all opposite i-contacts at distance two, retaining at most k−p_(T',i) even slots for its own window nonneighbors. Sum over both sides and all labels. Every outside-window high port contributes at least its one contact to the difference Σ(p_Ti−p'_Ti); every outside-window high nonport has an additional exact-distance-two cost at a nearest anchor. Thus

    X+Y ≤ 18k−5(w_A+w_B) ≤ 13k−5X,
    X+Y ≤ 6k+(7/6)X+1.

The maximum of the minimum of the two affine functions (without the last additive 1) is (6+49/37)k, achieved at X=(42/37)k. The possible low and six anchors increase the resulting order bound by at most eight. This contradicts the assumed lower order. Thus every high A member is a port and these high ports are not all private.

## Repeated use of the six-cut

Every two high A supports T,U satisfy |U−T|≤1, since otherwise the root on T, its anchor set, and a reduced cover of the other labels use only six roots covering B. This is the same argument as five-cut-large-degree.md, uniform in the cut size. Write C for their common labels, c=|C|, D=S−C, d=6−c. If d≥2, after deleting C the supports are singletons (optionally the empty set) or all co-singletons (optionally the full set). Decompose the B vertices using P_C,P_D,G,H as in that paper, with H the high B nonports having a distance-two label in C; H≤ck. For the singleton family, all residual nonport anchor incidences Q are at most X+d(c+1), and the representatives yield

    P_C+P_D+G ≤ dk+Q_G/d,

where Q_G counts the residual labels at exact distance two from the G nonports. This is exactly the d-representative bound in the five-cut paper; it uses P_D≤dk. For c=0 this is the excluded private case. Otherwise X≤k. When d≥4 the total n≤6k+(1+1/d)k+O(1)≤(29/4)k+13 contradicts the lower bound. The co-singleton count at d≥3 gives Y≤6k, also impossible. Hence c≥3. If d=2 the optional full or its absence is allowed. All these reductions apply to every minimum six-cut.

There must be a high private B port at a common label. Indeed suppose not. Apart from at most one common label i_0, the nearest set J of any high B nonport cannot be the singleton {i} with i in C: an immediate predecessor to such a nonport is private at i, and only one possible low predecessor exists. If some high A port is full, it covers all B ports and B depth-three vertices in one quota. All other high B members have depth two, and at most (d+1)k of these can have just one nearest label; every other depth-two member costs at least two units in the 6k anchor budgets. Thus Y≤k+(6+d+1)k/2≤6k, contradiction since d≤3.

If no high A member is full, necessarily d≥2, and the only remaining support situation is the residual singleton family: a d=3 co-singleton has already been excluded and the two co-singletons at d=2 are singletons. For the H high B nonports that have a common nearest label, either they consume two common-anchor units, or one such unit and a residual unit, except for at most k members at the exceptional singleton i_0. Therefore 2H≤ck+Q_H+k, with Q_H their residual incidences. Combining the preceding bound on P_C+P_D+G and Q_H+Q_G≤X+d(c+1)≤k+d(c+1) gives

    Y ≤ dk+(c+2)k/2+d(c+1)/2 < 6k

since d≥2, c≥3. This is also impossible.

Choose a high private B port v on a common i. If X≥k−5 it already sees that many distinct A vertices at distance two. Otherwise the high A degree bound forces X=k−6, |A|=k−5, with all high A members full to S and complete in A, and the low z in A. If z is a nonport, its distance to B is exactly two plus the anchor-depth, opposite in parity to any full high A vertex, giving |B|≤2k. If z touches i, choose v on that i. Indeed in this case every label has a high B nonport with that unique nearest label, since otherwise a full high A root and five anchors cover all of B. Its private predecessor is high, and sees all k−5 vertices of A.

Now W=N_B[v] has ambient boundary contained in i together with its second-layer vertices outside A. Thus |∂W|≤1+k−(k−5)=6. More than 6k/5 high B vertices lie beyond W and its boundary: there are at most 3k high B ports (at most k if a full A high exists, otherwise the ≤3 residual representatives cover them), and amongst high nonports W can contain at most k because each such member lies at distance two from i. Since Y>6k, even after the six boundary deletions more than 2k−6 remain. Consequently ∂W is a minimum six-cut and W is its smaller side. Its high member v touches only one of the new cut labels, contradicting the proved common-support lower bound of three for the smaller side of every minimum six-cut. This proves the theorem.
