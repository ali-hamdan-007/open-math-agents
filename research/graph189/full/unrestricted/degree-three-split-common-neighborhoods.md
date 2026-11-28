# Two separated ranges of common-middle degrees

In a high-order six-template degree-three residual, partition the h triple-visible remotes into a group B of g vertices and a group of r=h−g vertices. Suppose the latter each have at most d neighbors in W, the former each have at least g+2d+e+1 neighbors in W, and K=k−g satisfies

    K≥7d+100,       f+b+2r≥3(d+e)+2.

Then G is traceable. As e≤6 and f≥7, the second inequality follows from 2r≥3d+13. The parameter b counts pair-visible remotes and f is the sum of the anchors' positive even-distance counts outside the remote layer. No connectivity is assumed.

**The remote part.** Let L=R∖B be induced. As in the mixed theorem, |L|≤3K−f−b−2r, δ(L)≥D=K−d−e, and hence |L|+2≤3D. Also 2h≤k−6 by the visibility bound in R. If I is an independent set of D+1 vertices of L, any two members have a common neighbor in L by |L|≤3D−2. No member x of I sees a B vertex: it has at most d W-neighbors, and one B-neighbor would put at least g+d+e+1 W vertices at distance two from it, alongside D independent peers and a visible anchor. This exceeds k.

In fact no x∈I sees W. Otherwise it is triple-visible and has a W-neighbor w. Write g(w),r(w) for w's numbers of neighbors in the two triple groups. By degree w misses at most g(w)+r(w)+2 other W vertices. Thus at least |W|−d−g(w)−r(w)−2 W vertices have distance two from x via w. Every one of the g(w) B-neighbors of w has distance two from x as well, since x has no B-neighbor. Together with three visible anchors and D peers, the total is at least k+(k−h−2d−2e+1), greater than k because k−h≥(k+6)/2, k≥7d+100 and e≤6.

Every member of I thus has at least k−e+1 vertices in its closed L-neighborhood, as it misses W and all B. It has an exceptional supporting port J. As usual, |Sⱼ∩L|≤K−2, the boundary in L has size ≤e−2+aⱼ, and counting the aⱼ common neighbors of J, one anchor and the D peers at x gives aⱼ≤g+d+e−1. The k−e+1 closed neighbors are all in the closed support neighborhood but miss every other independent member of this support. Hence

    |I∩Sⱼ|≤1+(K+e−4+aⱼ)−(k−e+1)≤d+3e−5.

Summing over e exceptional supports contradicts K≥(e+1)d+3e²−4e. Therefore α(L)≤D and, if L is 2-connected, the Nash-Williams theorem yields a Hamilton cycle. If L is disconnected or has a cut vertex w, the bound |L|≤3D−2 gives exactly two parts after deleting zero or one vertex as applicable. Each has order ≤2D−3 and internal minimum degree ≥D−1, so endpoint-marker closure gives Hamilton-connectedness. Take two spanning cycles of the parts, incorporating w into the cycle of a part where it has two neighbors.

Reserve one true singleton-class private P and its solo for a single cycle. For two cycles choose distinct exceptional ports P,Q on the respective parts and different incident anchors. Both parts contain nontriples since D−r=k−h−d−e>0. Their total nontriple population is ≥c−h−1>k−h−2, which exceeds the number of nontriples in a single visibility class or port support. Distinct anchors may therefore be chosen; if the initial ports coincide, pair their common port (with its two available anchors) with a different port on either side. Unreserved exceptionals with aⱼ≤e can be inserted on distinct original directed cycle edges: their L-neighbor counts are ≥K−aⱼ−e−1 and external support boundaries have size ≤aⱼ+e−2, giving ≥K−4e+1≥e−1 eligible edges.

**The common-middle part.** Form the graph on W, B, and the at most e−1 remaining unreserved exceptionals, each with at least e+1 W-neighbors. Adjoin an endpoint marker at any two distinct W vertices. Its order N is at most k+g. Initially a W vertex has augmented degree at least k−3−e−r(w), as all g(w) of its B-neighbors are retained. Two W vertices can therefore be joined at cycle-closure threshold N whenever r(v)+r(w)≤K−2e−6. Now r(w)≤r≤K/2−3 by 2h≤k−6, and Σr(w)≤rd by the small group's W-degree bound. Every W vertex with r(w)≤K/3 qualifies with all W vertices (K≥100≥12e+18). Fewer than or equal to 3rd/K≤3d/2 vertices have larger r(w). After completing the other W vertices only these can still miss one another, so any remaining W pair has degree sum at least 2(k−e−1−3d/2)≥k+g from K≥3d+2e+2. Thus W is completed to a clique.

The B vertices have ≥g+e+1 W-neighbors, so they now pair with W degrees ≥|W|−1 at threshold N. Complete B to W, then complete each high exceptional to W using its ≥e+1 neighbors and the W degrees ≥|W|−1+g. In this closure each of the ≤g+e−1 vertices outside W and the marker can be put in a distinct gap of a W path with the chosen endpoints, since |W|−1≥g+e−1. Closing the path with the marker and reversing closure gives the desired original W-ended traversal.

Use the one-cycle global route W traversal, anchor-root path, reserved private and opened expanded remote cycle; or the two-cycle route opened cycle ending at x, P,a,z,c, W traversal, b,Q, opened cycle starting at y, with the three anchors distinct. These routes span G.
