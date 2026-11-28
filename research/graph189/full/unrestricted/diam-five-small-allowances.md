# The high-order diameter-five case has far allowance h≥8

Assume n>3s+2 and retain the notation and preliminaries of diam-five-end-allowances.md. Write P for the number of type L productive middle vertices and Q for the number of type H productive middle vertices. Put r=j+g+m+2. Every B has at least r anchor-neighbors, so every C is visible at distance two from at least r anchors. We give a direct proof excluding h=6 and a six-parameter integer check and structural proof excluding h=7.

## Two further inequalities

Fix an anchor x omitting precisely m vertices of B. At least c−h+m middle vertices are hidden from x, meaning that x has no length-two path to them. Any productive one among them must be H, and there are at most l such vertices in all. Since c≥h+l+g+2, some hidden middle vertex is nonproductive. Its B-neighbors are confined to the m omissions of x. Its D-neighbors are confined to D−D+, of order d0≤j since every F vertex misses all of them. Thus s≤c−1+m+d0, which gives

    c ≥ h+l+g+2+(i−m)+(j−d0).                                  (1)

We will use the weaker (1) with j−d0 dropped. More generally every nonproductive middle vertex needs at least s−c+1−j neighbors in B.

An L midpoint sees at most l far vertices and an H midpoint sees at most h anchors. If Pl<f, some far y sees no L; then the H midpoints must collectively cover all anchors, and Qh≥a. This y sees precisely Q members of C, its H midpoints. As in the previous note, at least i+Q B vertices have a neighbor in that set, and each such B omits at least a−h anchors. Counting all B omissions and all visible C vertices within the same aggregate anchor budget ah gives

    ah ≥ max(am,(i+Q)(a−h)) + (c−P−Q)r + Pa + max(Qr,a)       if Pl<f.
                                                                    (2)

If Pl≥f, the last maximum can be replaced by Qr, and the first maximum by max(am,a−h) if Q>0, or am if Q=0. Indeed even one H exhibits a B-neighbor omitting at least a−h anchors. The h=6 proof needs only the fully H case P=0 of (2). Notice also that P≤h−m, Q≤l, and Q=l precludes P>0 because every far vertex has already spent its entire C budget on H vertices, whereas an L midpoint must serve at least one far vertex.

## Excluding h=6 without computation

Here 10≤c≤11 and 2≤l≤3. Since c<(m+1)(6−m), necessarily m=2 or 3. The existence of an L midpoint would imply i+g+1≤l with i≥m, forcing i=m=2, g=0, l=3, c=11. But the prior covering estimate c≤(m+1)(h−m)−mP would give c≤10. Thus P=0. In particular Q≥2, since one H midpoint could not see all a>h anchors, and c−Q≥h+l+g+2−Q≥8.

Write t=j+g, so a=i+7+t, r=m+t+2. From (2),

    5a ≥ (i+Q)(a−6)+(c−Q)r.

The right side minus 5a is at least (i+2)(i+1+t)+8(4+t)−5(i+7+t)=i²−2i−1+(i+5)t. This is positive for i≥3 or t≥1 since i≥2, so i=m=2, t=0 and a=9. But cr≥10·4>9·4=a(h−m), contrary to the incidence bound.

## The h=7 arithmetic

The accompanying standard-library Python enumeration diameter_five_scalars.py uses (1), (2), and the earlier inequalities. For clarity, the complete list of its other filters is

    2≤l≤cmax−h−2,  cmax=floor((h+1)^2/4)−1,  a=i+h+1+j+g≤4max(h,l),
    i≥m≥1, j,g≥0,  c≥h+l+g+2,  c<(m+1)(h−m),  cr≤a(h−m),
    P+Q≥1,  P+Q≤c,  P≤h−m,  Q≤l,  Q=l implies P=0,
    P>0 implies i+g+1≤l and c≤(m+1)(h−m)−mP,
    Q>0 implies r≤h,  Pl≥f or Qh≥a.

When Q=0 it also tests existence of an integer t=|D+| between max(h+1,a−2l,1) and d satisfying f(t−l)≤tl, as established in the previous paper; t≥h+1 follows from the far vertex's minimum degree. These inequalities leave the following twelve rows compressed into five families. All have P=g=0. The graph proof below eliminates each family. Here j and Q multiple values are inclusive alternatives, while the listed (l,c,Q) triples are exact.

|i|m|j|Possible (l,c,Q)|
|--:|--:|--:|---|
|1|1|0,1,2,3|(2,11,2)|
|2|2|0|(2,11,2), (2,12,2), (3,12,2), (3,12,3)|
|3|2|0|(2,12,2)|
|3|2|0|(3,13,2), (3,13,3)|
|3|2|0|(2,13,2)|

The remaining quantities are fixed by a=i+h+1+j+g and s=a+l. In an all-H case at most l−Q members of B lack an H-neighbor, by the far-side covering inequality. Any B vertex with an H-neighbor has at most h anchor-neighbors, so since a>h it is omitted by some anchor. For a given anchor, its visible C vertices are exactly those having a B-neighbor outside its omitted B-set.

If i=m=1, each anchor omits exactly one B vertex. Since Q=l, all B vertices have H-neighbors and each is the unique omission for some anchor. Each such omission must hide at least c−h+1=5 middle vertices, all supported in B solely by that one vertex. There are b=i+l=3 different omitted singletons, so 15 different middle vertices would be needed, contradicting c=11.

If i=m=2, all anchor omission sets are pairs. Each pair hides at least c−7+2>c/2 middle vertices. Any two omission pairs must therefore intersect: a middle vertex hidden from both has a nonempty B-neighborhood contained in both pairs. Their family has no common member since every B has an anchor-neighbor. A pairwise-intersecting family of two-element sets with empty common intersection is a triangle, using only three B vertices. Therefore at least b−3=l−1 B vertices are never omitted. Each such vertex must lack an H-neighbor, but at most l−Q≤l−2 can lack one.

For the next two rows, every nonproductive middle vertex has at least s−c+1−j=2 neighbors in B. Take a minimum omission pair X and another anchor's omission set Y not containing X, which exists because each member of X has some anchor-neighbor. The middle vertices hidden from both have their B-neighbors contained in X∩Y, of size at most one. Hence all of them must be productive. Their number is at least c−14+|X|+|Y|≥c−10. But an anchor must see some member of the Q productive set, hence it can miss at most Q−1 of them. In those rows c−10≥Q, a contradiction.

The last row gives a=11, s=13, b=5 and two H midpoints. As Q=l=2, every B is adjacent to at least one midpoint. None can be adjacent to both: the two H visible-anchor sets together cover all eleven anchors and each has size at most seven, so their intersection has size at most three, whereas every B has at least r=4 anchor-neighbors. Hence the five B vertices split into the disjoint B-neighborhoods of the two H midpoints. Each H has a private anchor (one for which it is the only visible H) because the other H sees at most seven anchors. Such an anchor misses the entire opposite B group. With i=3, the two groups therefore have sizes two and three.

An anchor private to the two-element group misses all three opposite B vertices and sees both members of its own group. It sees at most 7−3=4 middle vertices. At least nine of the thirteen middle vertices consequently have all their B support in the three-element group. An anchor private to that larger group misses both members of the smaller group. It must also miss a member of its own group: otherwise it would see all nine middle vertices. It now has the maximum three omissions and sees at most four of those nine. Thus at least five of them have B support equal to the single omitted member of the three-element group. But each B vertex has at most h−m=5 middle neighbors, and this B vertex also touches its H midpoint, whose support is the entire three-element group. This is a contradiction.

Hence no high-order qualifying graph of diameter five has h≤7. At h=7 the only numerical computation enumerates elementary inequalities on bounded integers.
