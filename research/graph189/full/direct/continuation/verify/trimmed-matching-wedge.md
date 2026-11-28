# The matching penalty after deleting large-degree vertices

Retain the setup and original-graph quantities b,E of ../root/trimmed-high-degrees.md. If an induced wedge in H has positive defect j_H, then its original defect j is at least 1−b and the candidate count K=1+E−j is at most E+b. In particular E+b≥0. If E+b≤floor((k−1)/2), the local matching bound and monotonicity of f(i)=i(k−1−i) up to that threshold give

    n≤3k+1+b+(E+b)(k−1−E−b).

This is a sufficient large-order test for rooted traceability after the deletion T, with the same connectivity and near-spanning size assumptions as in the earlier deletion paper.

Suppose now that at most two vertices have degrees greater than k, with no bound on their degrees and any one vertex of degree less than k allowed. For k≥16 the whole graph is traceable, at every order and connectivity. Indeed the prior vertex-cut theorems allow κ≥3. Delete the at most two higher-degree vertices, leaving a connected H, and choose z of minimum original degree in H. Every other surviving vertex has degree k in G. Each surviving induced wedge with endpoints different from z has E≤0 and b≤2. A positive H defect would therefore give 0≤E+b≤2 and n≤3k+3+2(k−3)=5k−3. At n>5k−3 the rooted local Ore theorem yields a path spanning H and the almost-spanning theorem yields a spanning path of G. At n≤5k−3 use ../global/five-times-order-unrestricted.md.

## All k with at most two vertices above k

In fact the same theorem holds at every k. Cases k≤5 and κ≤2 are already known, and the preceding large-order matching argument works for every k≥6. At n≤5k−3 use the unrestricted-degree part of ../global/max-degree-plus-two-exception.md, through its deduction that the only residual has k≥8, a longest path P and an exterior clique C of size k−2. All high members of C see the same three marks A, which contain all its path contacts. We also have n≥5k−4 and |P|≥4k−2.

There is a mark i touching all of C. This is immediate if C is wholly high or its low member touches at least one mark. If the low z∈C touches none, divide V−(A∪C) into X,Y,Z at distance 1,2,≥3 from A. A high C member sees X and Z at positive even distance (each Z is high, so its distance is four); z sees all Y at distance four via a high C member and a mark. Thus |V−C|≤3+2k<4k−2.

Each of the two immediate P-neighbors w of i misses C and sees all its k−2 vertices at distance two. At most two other vertices are positive-even from w. As the fourth layer would separate any fifth layer and G is 3-connected, its eccentricity is at most four. Every distance-three target outside C has a penultimate in C or among those two extra even vertices. The former targets belong to A and i is already adjacent to w. Each fixed outer penultimate serves at most k targets since its first-layer predecessor sees those targets at distance two. Hence |V−C|≤1+d(w)+2+2k+2, giving d(w)≥2k−7>k for k≥8. These two bracketing vertices are distinct and lie outside A, since every gap around the marks contains ≥k−2 unmarked vertices. They exhaust the permitted vertices of degree above k, so every mark in A has degree at most k.

Orient P so that all three mark successors are high. This is possible even if the low lies on P because the large gaps prevent it from being both a preceding and a following neighbor of marks. At any high x∈C the rooted local defect sum is at least three, whereas each wedge from x via its mark to its successor has both endpoints high and center degree at most k. The original order bound makes every such defect nonpositive since n≥5k−4>3k+1, a contradiction. This proves the all-k result.
