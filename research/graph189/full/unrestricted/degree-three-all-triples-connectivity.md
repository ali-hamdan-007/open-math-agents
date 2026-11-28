# Removing the connectivity hypothesis from the all-triples routing theorem

In the six high-order degree-three templates of `degree-three-all-triples-routing.md`, G is traceable whenever k≥7h+84, without any connectivity hypothesis on the induced nontriple graph F.

We use the same selected induced graph L=F∪Z, r=|Z|, and notation ℓ=|L|, b,f,e,h as in that paper. If L itself is 2-connected, its proof applies unchanged: 2-connectivity of F had only supplied 2-connectivity of L; when r=0 the two graphs coincide. We treat disconnected L or connected L with a cut vertex. The fact that every member of L has a middle neighbor and none has a W-neighbor will be used throughout.

In the large expenditure case b+f≥3e+2 put s=e; as before every L vertex has at most s middle neighbors. Otherwise, when a private is doubled and r>0 put s=4, and in all other cases put s=3, with one refinement: if a private is doubled, r=0 and b=0, set s=2, since every member is exclusive. Set D=k−h+r−s. We have δ(L)≥D and

    ℓ≤3k−f−b−3h+r,      ℓ−3D≤3s−f−b−2r.

If L is disconnected, put j=0 and take its components. If L is connected with a cut vertex w, put j=1 and take the components of L−w. In both cases every part has order at least D+1−j.

**There are exactly two parts.** In the disconnected case it suffices that ℓ≤3D+2. In the large expenditure case ℓ≤3D−2. In the other case with s≤3 the bound follows from f≥7, and when s=4 one has f≥8 and r≥1, again giving ℓ≤3D+2. For the cut case suppose there are at least three parts, choose a neighbor xᵢ of w in each of three distinct parts and let aᵢ count the w-neighbors in that part. Put a=Σaᵢ. Each xᵢ sees the a−aᵢ contacts of the other two parts at distance two, besides at least one visible anchor at distance two. Thus 2a≤3(k−1). The closed neighborhood of xᵢ within its own part has at least D vertices, at most aᵢ of which see w. The others have distance two from w. These three sets are disjoint, and w has its own visible anchor, so 3D−a≤k−1. This gives 6D≤5(k−1), hence k≤6h+6s−5≤6h+31, contrary to the hypothesis.

**Each part is Hamilton-connected.** Write X,Y for the parts. Either has order m≤ℓ−j−(D+1−j)=ℓ−D−1 and internal minimum degree at least D−1. If ℓ≤3D−2 then m+1≤2D−2. Adding a degree-two marker at any prescribed pair and applying cycle closure at the augmented order m+1 completes all original vertices, giving the prescribed spanning path on reversal of closure.

Suppose ℓ>3D−2. The large expenditure case was already covered, and f+b+2r≤3s+1. In particular at most b+r≤3s+1−f≤6 vertices in either part are nonexclusive, since now s≤4 and f≥7. Put q=1 if privates are all singletons and q=2 if one is doubled. Each exclusive vertex has degree at least k−h+r−q−1 in its part. The bound for m gives

    m+1≤2k−2h−f−b+s.

Also f+b+2r≥s+2q+2. For singleton privates the right side is seven and f≥7. For doubled privates with r≥1 it is ten and f≥8. For doubled privates with r=0,b≥1 it is nine and f+b≥9; if r=b=0 our s=2 gives eight, met by f≥8. It follows that the exclusive vertices can all be completed to a clique in the same endpoint-marker closure.

Let p≤6 be the number of other part vertices. Every such vertex has degree at least d=D−1≥k−h−7≥77. An exclusive vertex now has degree at least m−p−1. Since p≤d−2, each remaining exclusive–nonexclusive edge can be added at threshold m+1. The final nonexclusive pairs also qualify: if 2d≥m+1 their original degrees suffice, while otherwise m≥2d≥2p+1 and each sees m−p exclusive vertices. Closure thus gives Hamilton-connectedness for arbitrary specified distinct original endpoints.

**A pair of disjoint cycles and placement of the exceptional ports.** Each part has at least three vertices and a Hamilton cycle: select the ends of any internal edge, find the prescribed spanning path and close it with that edge. In the cut case the high degree D of w ensures two distinct w-neighbors in some part. Take a spanning path there between two such neighbors and close it through w; take an ordinary spanning cycle of the other part. This gives two disjoint original cycles covering L in both cases.

Choose distinct exceptional ports P,Q with contacts x∈X and y∈Y, and distinct anchors a,b seeing P,Q respectively. Here is the choice in detail. The set of possible anchors in each part is nonempty. Unless one can choose distinct anchors from the two parts, both anchor sets are the same singleton, so every vertex of X∪Y lies in that one visibility class of size ≤k−2. But |X|+|Y|≥2D>k. Given distinct anchors, choose corresponding ports on their respective sides. If they are equal to a common port J, its mask contains both anchors, giving two choices at J. Some other exceptional port K sees a vertex in X∪Y, since |Sⱼ|≤k−2. Use K on the side it touches and J on the other; choose at J an anchor different from one incident to K. This produces the required distinct ports and anchors.

Reserve P,Q for joining. Apply the three cycle-edge insertion counts of `degree-three-all-triples-routing.md` on the union of the two oriented cycles. These counts still hold because the successor is injective on every subset of the union. Neighbors of each candidate vertex in L all lie on one of the two cycles. Their eligible original edges across both cycles therefore number at least h+e−1 for every candidate. There are at most h+e−2 candidates. Subdivide distinct eligible original edges, yielding two disjoint expanded cycles. Assign the remaining triples and unreserved ports their pairs of W neighbors just as in the same paper. Its compatibility graph produces a spanning W-block traversal with first and last vertices in W.

Open the expanded cycle containing X so that it ends at the reserved contact x. Open the expanded cycle containing Y so that it starts at y. Let c denote the anchor different from a,b. Traverse the first opened cycle, then P,a,z,c, then the W-block traversal, then b,Q and the second opened cycle beginning at y. The endpoints of the W-block traversal see c and b, respectively, and all other joining edges were chosen explicitly. The path spans G.

This finishes the disconnected and cut cases and removes the connectivity hypothesis entirely. The remaining high-order degree-three problem must have k<7h+84, equivalently h>(k−84)/7, if it is nontraceable.
