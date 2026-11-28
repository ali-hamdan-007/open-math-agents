# Connectivity two for k≥8 using the tight cut and stronger counts

This refines the [high-degree two-cut proof](high-degree-two-cut.md). The original conjecture holds on paper for every graph of connectivity two and second-smallest degree k≥8. The balanced side routing and the construction of the recut are the ones proved in that note. The changed estimates below handle the smaller threshold.

## Lower order and triangles

The degree-two theorem gives minimum degree at least three. The checked tight-two-cut theorem eliminates a low min-degree vertex on a two-cut, since the anchor-degree bound would force its degree to be k−1. Therefore the linked-set lower-order argument uses degree bound k even in the critical completion case where a minimum vertex belongs to a cut. The construction at parameter three uses k≥8. The rooted matching order in the Hamiltonian-deletion case also applies. Accordingly every counterexample has n≥4k−5. This exceeds 3k+2 for k≥8, so every edge lies in a triangle by the prior edge-order bound.

The original minimum-component choice and the three-component exclusion work at k≥8, and all balanced-side inequalities still hold. In particular 3(k−2)>2k−1, 3k−5>2k−1, and 2(k−3)≥k+1. The balanced construction misses at most five vertices, within the allowance h+1 with h=ceil(k/2).

## Common-free A

Keep the notation of the high-degree proof. If B is also common-free, its port apex replaces each high vertex's only lost anchor edge, so Fan applies with threshold k instead of k−1. The B path is rooted at a port and covers at least min(b,2k−1).

Suppose B has a common port. If the anchors are adjacent, all high vertices in each side are at distance at most two from some anchor because the opposite side has at least k−1 high vertices. The even rows of adjacent p,q therefore cover every vertex except common ports and a possible low vertex. A private contact in A sees q and all t common B ports at distance two, so t≤k−1. Including each anchor's distance zero, this gives n≤3k+2, impossible. If p,q are nonadjacent, they are at distance two through a common B port. The two anchor rows spend two additional places on one another.

In either possible case let j be 0 if B is common-free and 1 if B has a common port. The census reads

    b ≤ 2k−2+w+l−t
    a−l_A+r+v+2w+2j ≤ 2k.

Using a≥k, t≥j, v,r≥0, and substitution for w gives 2b≤5k−4+l_A+2l−4j. As before a≤2k−2 if A is wholly high, and a≤2k−3 otherwise. Dirac gives an A path from either anchor losing at most l_A. The B-apex path covers at least min(b,2k−1−2j). With the unused anchor the total omission is at most

    floor((k−4+l_A+2l)/2) + 2 + l_A ≤ h+1.

For l_A=1 use l=0. For l_A=0 use l≤1. This closes the common-free case.

## Shallow A with both private types

The private representatives give b≤2k−2+w+l−t as before, with c common A ports, t common B ports and l low B nonports. Each high vertex is within distance two of some anchor. For adjacent p,q, a high vertex of odd distance from both anchors must be common, while w vertices are counted in both inclusive even rows. Thus n+w≤2k+3+c+t. Since b≥2k we have w≥2−l+t, and c≤k−1 because A has a private contact. So n≤3k+1.

If the anchors are nonadjacent, their mutual distance is two. Write L=l_A+l_B. A common A port bounds the number of B ports by k. The two anchor rows therefore give a−c−l_A+v+2w+2≤2k and v+w≥b−k−l_B, hence n+w≤3k+c+L. Its combination with the first inequality and c≤a−2 gives

    2b ≤ 5k−6+L+l−t.

Also a−c≤k−4+L+l−t, using b≥2k and w≥2−l+t. Each anchor contacts at most k vertices of A, so a+c≤2k+l_A. Consequently

    2a ≤ 3k−2−t.

If A is wholly high, its internal minimum degree k−2 suffices for a Hamilton cycle, as a≤2k−4 for k≥8. When A contains a low vertex z, the remaining side has minimum degree at least k−3. It is Hamilton-connected by Ore if k≥9 or if k=8 and t≥1, since in these cases 2(k−3)≥a. If the chosen anchor touches z, start there and enter the core at any internal neighbor. Otherwise z has at least two internal neighbors, because its original degree is at least three and it misses the chosen anchor. Start at a contact of the chosen anchor and span the core to a different neighbor of z, ending at z. This always spans A.

If t=0, the strengthened Fan path covers min(b,2k−1), with b≤floor((5k−4)/2). If t≥1, Fan covers min(b,2k−3), with b≤floor((5k−5)/2). In each case the B deficit plus one unused anchor is at most h+1. The sole exceptional routing case k=8, t=0 with low z in A still works. Here a≤11, so Dirac in A−z supplies the path missing at most one vertex, and b≤17 from L=1 and l=0. The B path covers at least 15 of these vertices. The total omission is at most four.

## Recut estimates and the early equality cases

Consider the shallow case missing the q-private type. All high A vertices touch p. If the A p-contact count is k, its opposite contact is internally universal and b≤2k, while a≤k+1. For k≥8 the only way n≥4k−5 can hold is k=8, a=k+1 and b=2k. Then the low vertex z lies outside those A contacts and is a nonport. The B p-contact count must equal k, because p's even quota bounds its B noncontacts by k. Therefore every A p-contact is internally universal. Each also touches q, since a private one would see q at distance two through a q-contact along with the k opposite p-contacts. Thus all high A vertices are common. The high common vertex and z have complementary parities to every B vertex, by the same cut metric as in the original note, and z spends two even places on the two anchors. This gives b≤2k−2, a contradiction.

We then choose p with exactly k−1 contacts in A as before. It follows that a≤k. In the common-B-contact torso alternative, b≤2k+1. The only possible equality with n≥4k−5 is k=8, a=k, b=2k+1. Again A must contain a low nonport z, with all high vertices touching p. There are at least k B contacts of p because its even row counts every noncontact except at most one. So there are exactly k, forcing the A p-contacts to be common by the same saturation argument. The complementary parity at a common A vertex and the low nonport gives b≤2k−2. The edge-between-labels and edge-between-private-types alternatives both have b≤2k and a≤k, an immediate contradiction for k≥8.

In the recut construction, as in the previous note, a high private vertex in A is impossible. Let m=a−l_A be the number of high A vertices, all common. The bound on |W_high| is k−2 if w touches q, and k−1 otherwise. At the high q-contact f in W the even row counts all m high A vertices and U₀. Thus at most k−m−|U₀| vertices at distance four from f remain. Among high U vertices other than U₀ and these exceptional vertices, all have distance two from w. If w misses q, it sees q at distance two via f, so at most k−1 of them are available, and otherwise at most k. In both cases

    |U_high| + |W_high| ≤ 3k−m−2.

Allowing the gate w and any low B vertex, b≤3k−m−1+l_B. Adding a and the two anchors gives n≤3k+1+l_A+l_B≤3k+2. This excludes the final case.

## Degree seven

The more general checked index-three argument also gives n≥23 at k=7. Its original boundary hypothesis 2·3+2≤k is replaced at this degree by a separate linked-witness construction. The equality order n=23 is covered by the [moderate-order paper proof](../../root/moderate-seven-eight.md), so a counterexample has n≥24 and every edge is in a triangle. The minimum-component choice, the balanced route and the common-free arithmetic remain valid.

In the large-side case with both private types, the adjacent-anchor parity argument still gives n≤3k+1. For nonadjacent anchors with no low vertex in A, the bound 2a≤3k−2−t still allows Dirac in A at k=7. When a low vertex lies in A, the high core has order at most eight and internal minimum degree at least four, so Dirac produces a path from the chosen anchor losing at most one. Now L=1 and l=0. The bound on 2b gives b≤15 if t=0 and b≤14 if t≥1. The respective B paths cover at least 13 or 11 vertices. Including the unused anchor gives at most four or five omissions, within h+1.

In the remaining shallow recut case, either early upper bound n≤3k+3 can meet n≥24 only at equality. Both arguments at the previous threshold k=8 rely only on equality in those size counts and the positive even quotas, and prove b≤2k−2 in either equality case here as well. The final recut bound n≤3k+2 again contradicts n≥24.

Thus the first degree below this paper route is k=6. The tight-cut and index-three theorems passed the pinned kernel separately. The full separating-pair assembly and the k=7 moderate boundary routing are still paper proofs.
