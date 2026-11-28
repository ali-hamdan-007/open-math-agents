# A shallow small side with a double port at a minimum three-cut

Let κ(G)=3, k≥24 and G−S have sides A,B for a minimum three-cut S. Suppose |A|≤2k−5, every high A vertex touches S, there is an A port touching exactly two anchors, and no A port touches all three. Then G is traceable, at arbitrary |B| and with the possible unique low in any location. The prior shallow-universal and private-port arguments cover the complementary support families. The argument uses the five-times-order theorem and the coordinator's first-step observation.

Assume n≥5k−2. Write a_h,b_h for the high-vertex counts outside the separator on each side, so n≤4+a_h+b_h. A has a high vertex: otherwise it is a low singleton and connectivity would force it to touch all three anchors. Every high A vertex has internal degree at least k−2, so |A|≥k−1 and a_h≥k−2. Every high nonport of B has depth exactly two from S: at depth at least three it would see all opposite high A vertices at distance four and have at least three other even vertices in its second layer, exceeding k. Write J(x) for the nonempty nearest-anchor set of any such B vertex. Every anchor has a contact on both sides.

For a port u in A with r anchor neighbors, at least 3−r of its positive-even vertices lie in A∪S: the boundary of its closed A neighborhood separates this neighborhood from B, and all boundary vertices other than the r incident anchors are at exact distance two from u. Each A port sees all opposite ports having an intersecting anchor support at exact distance two. A high A port additionally sees at exact distance four every high B nonport x with disjoint nearest-anchor set, since a length-three crossing would require x's nearest-anchor set to meet its opposite port's support.

If a double A port u (also permitted to be low) has a high singleton A port v on the missing anchor j, then three even sets cover all high B vertices: use u,v for all B ports, use v for B nonports with j∉J(x), and use anchor j for B nonports with j∈J(x). The first two roots spend at least one and two slots outside B, so b_h≤3k−3. This contradicts n≥5k−2 as |A|≤2k−5, allowing even the extra potential low in B. From now on no high singleton is complementary to an occurring double support.

If precisely one double support occurs, its missing anchor j has at least one A contact. All such contacts would now have to be a single low singleton z. But the edge jz then lies in no triangle: z lacks other anchor neighbors and A has no other j-contact. This contradicts the registered edge bound that a triangle-free edge forces n≤3k+2.

If all three double supports occur, choose one A representative of each type, high where possible. Each high B port is at distance two from at least two representatives. Each B nonport with a one-element J is at even distance four from the representative missing that anchor whenever that representative is high. Let q₁,q₂ be the numbers of high B nonports with respectively one or at least two nearest anchors. Let q_bad=0 if all representatives are high, otherwise let it count the singleton nearest class corresponding to the sole low representative; q_bad≤k by that anchor's budget. If p is the number of high B ports then

    2p+q₁−q_bad≤3k,       q₁+2q₂≤3k,
    b_h=p+q₁+q₂≤3k+q_bad/2.

All high A vertices must be double ports, since every singleton is complementary to one of the three types. Each anchor has ≤k A contacts by an opposite port, so a_h≤3k/2. If q_bad can be nonzero, all high double ports have just the two other types, which share an anchor, giving the stronger a_h≤k. In either case n≤4+(9/2)k≤5k−3.

It remains to treat exactly two double supports. Label them 12 and 23. Every high A port then touches 2, since the only allowed high singleton is 2. Thus a_h≤k and m=|B|≥4k−6>3k under the large-order assumption. For any A vertex y, shortest paths from y to the three distinct anchors cannot begin collectively with just two different vertices. If they could, choose the two first steps v,w. Given any B vertex x odd from y, select an anchor on a shortest crossing y-to-x path; the chosen first step toward that anchor can be followed by a geodesic to the anchor and the same suffix to x. Its distance to x is then exactly one less than the odd y-to-x distance, and is positive even unless the step equals x (impossible since the step belongs to A∪S). Thus E(y),E(v),E(w) would cover all of B, impossible at m>3k. This observation allows low as well as high roots.

Every A port y touching 2 sees any missing i∈{1,3} at distance two. Indeed d(2,i)≤2 via the corresponding double, so d(y,i)≤3. Equality gives a shortest first step 2 toward both i and 2, leaving only one more first step needed for the third anchor, just excluded. In particular this applies to both chosen double representatives, regardless of degree. They pay all high B ports at distance two. A B nonport whose nearest set is just {1} or {3} is at distance precisely four from the double port missing that anchor: the lower bound is by the crossing criterion, and the upper bound follows through its missing anchor at distance two even if the port is low. Any still unpaid nearest set contains 2 or contains both 1 and 3.

Writing Q_i for the number of high B nonports at distance two from i and p_i for the high A contacts of i, one gets Q_i≤k−a_h+p_i since all high A noncontacts of i are at distance two. Moreover p₂=a_h and p₁+p₃≤a_h. Consequently

    b_h≤2k+Q₂+(Q₁+Q₃)/2≤4k−a_h/2,
    n≤4+4k+a_h/2≤4+9k/2≤5k−3.

This finishes the last support pattern.

## Removing the side-size restriction in further cases

The arguments with no complementary high singleton did not use |A|≤2k−5. They give traceability at any |A|. When a complementary high singleton exists one can always improve b_h≤3k−3 to b_h≤3k−4: its anchor j has an additional positive-even witness in A, since its nonempty proper A-contact set (the complementary double misses j) has an edge in the connected A leading out of that set. Thus the small-side argument also covers |A|≤2k−4 (allowing one possible extra low B vertex).

Moreover if B contains any multiport, then a_h≤2k−3 at every order. Its universal port alone gives a_h≤k. Otherwise take a B double and any B port touching its missing anchor. These two see every A port at even distance two. If the latter is a singleton their own-side boundary costs at least 1+2 slots, and if it is another double their boundary costs at least 1+1 while an A contact on the overlapping anchor is counted twice. Therefore n≤4+b_h+a_h≤5k−3 with no restriction on either order. This leaves, for large shallow A with doubles, only the case with a complementary high singleton in A and exclusively singleton ports in B.
