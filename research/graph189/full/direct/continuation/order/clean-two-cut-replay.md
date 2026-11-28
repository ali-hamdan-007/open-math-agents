# Two private representatives in the separating-pair paper

Fix a separating pair {p,q}, and write A and B for its sides. Suppose u and v in A have distance vectors (1,2) and (2,1) to p,q. For a vertex y in B of vector (a,b), the distances from u and v are min(1+a,2+b) and min(2+a,1+b). A shortest walk must cross one of the two anchors, which proves these formulas in the ambient graph.

Every port in B contributes once to the even-distance budgets of u,v, and every common port contributes twice. A nonport at distance two from only one anchor contributes at the opposite representative. The two exceptional sets are W, the nonports at distance two from both anchors, and F, the vertices at distance at least three from both. Write T for the common ports. The two representatives also spend one place each on the opposite anchor. Thus

    |B| + |T| + 2 ≤ 2k + |W| + |F|.

Lean 4.33.1 checked this implication directly on the graph, with only propext, Classical.choice and Quot.sound. It does not assume a degree lower bound at the representatives or at vertices of B. [Checked source](Graph189PrivateRepresentativeBound.lean) · [Original paper paragraph](../sep/unrestricted-two-cuts.md#local-counts-and-routing)

## Remaining clean-side assembly

A common-free side A is clean when every high private port is at distance two from the other anchor and every high nonport is at distance two from both. Let H be the set of high A vertices and let r(A),r(B) count the nonports in the two sides. The two second layers of p and q count all H once, each high A nonport once more, and each B nonport outside F once, counting W twice. The distance-two budget at each anchor is k.

Every high y in F would see every high A vertex at distance four. The minimum-separator boundary inequality charges two additional places to y because it has no port. This forces |H|≤k−2. But a high vertex in a common-free side has at least k−1 internal neighbors, so |A|≥k and |H|≥k−1. High vertices in A exist since the two distinct representatives cannot both have degree below k. Consequently F consists only of a possible low vertex. Counting the disjoint low populations of A and F and adding the two inequalities gives

    n + r(A) + r(B) + |T| ≤ 4k + 2.

In the common-free case on both sides, the verified counterexample order lower bound n≥4k−5 yields r(A)+r(B)≤7. Each side contains at most k−1 contacts of either anchor because the opposite side has a private contact of that type. A side with r nonports therefore has order at most 2k−2+r, and at most k−1+r of its vertices miss the selected anchor. Each side has at least four marked contacts when k≥26, by subtracting the opposite order and these noncontacts from n≥4k−5.

On a wholly high side, internal minimum degree k−1 gives a route from the selected anchor with at most 2r+1 losses by the checked longest-path and rotation lemmas. On a side containing the low vertex z, deleting z still leaves internal minimum degree at least k−2. When that graph is connected, the same argument loses at most 2r+3 including z. If deletion of z disconnects the side, the two separated parts each have minimum degree at least k−2, and their orders are small enough for Hamilton-connected closure. Three surviving marked vertices ensure two marks on one part, so that a mark distinct from a neighbor used at z can start a spanning route. This is the two-endblock construction used in the paper. The two anchored routes together miss at most 2(r(A)+r(B))+5≤19 vertices, within the checked terminal omission bound for k≥26.

The counts, marked routes and final graph-facing assembly in this section are under kernel replay. The first displayed inequality is already kernel-verified. Together the two sections implement the clean branch of the original common-free separating-pair proof. The cases with neither side clean use the separate defect and routing paragraphs.
