# Connectivity for a bounded local excess and large second degree

Suppose the rooted local excess is at most r in the sense of local-excess-connectivity.md. For every integer r≥3 write s=ceil(3r/2). If

    k≥(4r+12)(s+5) and κ(G)≥s,

then G is traceable. The excess can in particular be taken to be Δ−k when the prescribed root has minimum degree.

Take n≤(r+3)k+1 by rooted local Ore and optimize the choice of unrooted longest path and smallest high-containing exterior component as in ../global/two-thirds-exterior-degree.md. Let B be the whole 2-connected component or a terminal block with all noncut vertices high. Write b=|B| and let q be the minimum internal degree of the high, nonexceptional vertices (exclude the articulation or unique low). Each satisfies 3q≥2k−2r−4. Indeed if 3q≤2k−3, then (q+1)(2k−3q+1)≤n+1. Since q≥ceil(k/2), this gives 2k−3q+1<2r+6; integrality gives the claim. Otherwise it is immediate.

For b≥2q−1 the Fan theorem gives a disjoint cycle of length d≥2q−1≥(4k−4r−11)/3, larger than s. Menger and the cycle splice from the previous proofs give n≥(s+5)d/2. This exceeds (r+3)k+1 because (4s−6r+2)k≥2k>(s+5)(4r+11)+6.

Now take b≤2q−2. Apart from the possible exceptional vertex, B has internal minimum degree ≥q, so B minus that vertex is Hamilton-connected and B itself has a Hamilton cycle. The degree-two marker closure gives spanning paths between all pairs except possibly one pair (the two neighbors of the exceptional vertex when this has degree two). Put h=ceil(k/2).

If b≤k−1, the previously established bounds in local-excess-connectivity.md apply with s contacts: n≥(a+2)b+a for a=k−b+1 and n≥(s+2)b+s−(floor(b/2)−1). The proof there only uses κ≥s and h≥s here. In the terminal case the outside and two extended tails recover the one mark/gap lost by matching s−1 contacts. The first bound and b≥k/2 imply b≥k−2r−3, since (k/2)(k−b+3)≤n≤(r+3)k+1. The second bound yields

    n≥(s+3/2)(k−2r−3)+s+1>(r+3)k+1.

For the last inequality use s−r−3/2≥1/2 and k≥(4r+12)(s+5).

Finally if b≥k, a whole component has the same second bound from its s disjoint contacts and at most one exceptional interval. For a terminal B delete its cut vertex w to match s−1 ports in B−w. This graph is Hamilton-connected, so every gap and both tails have ≥b−1 vertices. Each tail can additionally traverse w by ending at another one of its at least two B-neighbors. Including the exterior B and its nonempty remainder therefore gives n≥(s+1)b+2>(r+3)k+1 since s+1≥r+3. This completes the proof.
