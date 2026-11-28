# Routing every triple-visible vertex in the six degree-three templates

Use the notation and six high-order templates of `degree-three-nontriple-cycle.md`. The root z has degree three and eccentricity three; the graph has order greater than 3k+2, and all other vertices have degree at least k. Every vertex has at most k other vertices at positive even distance. The three anchors touch k middle vertices: W, the set adjacent to all anchors, together with e exceptional ports, 4≤e≤6. Put R=L₃(z); its order c is at least 2k−1. Write h for the number of triple-visible remotes, b for the number visible to exactly two anchors and F for the nontriple induced remote graph.

**Theorem.** If F is 2-connected and k≥7h+84, then G has a Hamiltonian path. There is no restriction on how many common middles a triple sees.

For anchor i let Vᵢ be its visible remotes, fᵢ its even witnesses outside R and f=Σfᵢ. The template arithmetic in the preceding paper gives fᵢ≥2, f≥7, and f≥8 when a private class is doubled. Each nontriple has at most three exceptional port neighbors, since an anchor to which it is invisible misses at most three middles. An exclusive has at most two port neighbors in doubled-private templates and just one in all other templates. Let Sⱼ=N(J)∩R for an exceptional port J, Hⱼ=Sⱼ∪N_R(Sⱼ), and aⱼ=|N(J)∩W|. As before

    |Sⱼ|≤k−2,    |Hⱼ∖Sⱼ|≤e−2+aⱼ,    |Hⱼ|≤k+e−4+aⱼ.

The boundary inequality counts missed W through an incident anchor, z and a missed anchor adjacent to one in the port's proper mask. The anchor graph is connected in each template. Each w∈W misses at most h+2 others in W by degree, since outside W it sees only anchors, exceptional ports, and triples.

## Selecting an induced graph with a Hamilton cycle

Select a set Z of zero-W triples and put r=|Z|, L=F∪Z induced, and ℓ=|L|. When b+f≥3e+2 put every zero-W triple in Z. Otherwise put in Z precisely the zero-W triples with only singleton-mask ports as their middle neighbors (including both twins when available). In this second case b≤3e+1−f≤12. All members of Z have at least k−e−(h−1)≥2 neighbors in F, so adding them preserves 2-connectivity. By anchor visibility counting,

    ℓ≤3k−f−b−3h+r.

In the first case set s=e. In the second take s=4 if one private class is doubled and s=3 otherwise. Every vertex of L has no W-neighbor and at most s exceptional neighbors. In particular its L degree is at least D=k−h+r−s and its closed neighborhood within R has at least k−s+1 vertices. When r=0 the preceding nontriple-cycle theorem already proves L Hamiltonian; its degree threshold holds since e≤6. Thus it suffices to treat r≥1.

We first prove every pair of vertices in an independent I⊆L of size D+1 has an original common neighbor in L. When b+f≥3e+2, one has 3D−(ℓ+2)≥f+b+2r−3e−2≥0. Then the two degree-D neighborhoods in the ℓ−D−1 vertices outside I intersect. In the second case, put sₓ=|N(x)∩L₂(z)|. For distinct x,y∈I their L-degree sum is at least 2k−2h+2r−sₓ−sᵧ, whereas ℓ−|I|≤2k−2h−f−b+s−1. Thus it suffices that sₓ+sᵧ<f+b+2r−s+1. In a doubled-private template the left side is at most 4+b+2r: an exclusive has at most two middle neighbors, a pair-visible vertex three and an included triple four. The right side is at least 5+b+2r. Otherwise the left side is at most min(6,2+2b+2r) and the right side at least 5+b+2r. For b≤2 use the second bound on the left and for b≥3 the first. This proves the common-neighbor property.

For x∈I∩Sⱼ, its independent peers, the aⱼ W-neighbors of J and an anchor are disjoint distance-two witnesses. Thus aⱼ≤k−D−1=h−r+s−1. All of N_R[x] is contained in Hⱼ and misses every other member of I∩Sⱼ. Hence

    |I∩Sⱼ|≤1+|Hⱼ|−(k−s+1)≤e+s−4+aⱼ≤h−r+e+2s−5.

The e exceptional ports cover I (even a zero-W triple has some preceding port). Summing and substituting |I|=k−h+r−s+1 contradicts

    k ≥ (e+1)(h−r)+e(e+2s−5)+s,

which follows from k≥7h+84 since e,s≤6. We have proved α(L)≤D.

To obtain Hamiltonicity it remains to check that every independent triple has degree sum at least ℓ+2; the degree sum is already at least 3D≥3α(L). In the first selection case, 3D≥ℓ+2 was proved above. In the second selection case it suffices that the three middle-neighbor counts sum to at most f+b+2r−2, by the order bound on ℓ. With a doubled private the sum is at most 6+b+2r, which suffices as f≥8. Without a doubled private the sum is at most min(9,3+2b+2r). For b≤2 this is at most 5+b+2r. For b≥3 and r≥1 it is at most 9≤5+b+2r. We may now apply the independent-triple degree-sum criterion of Bauer, Morgana, Schmeichel and Veldman to the 2-connected L. It has a Hamilton cycle.

## Inserting every remaining vertex

Fix this oriented L-cycle. For any external vertex x with X=N(x)∩L, at least |X|−|D₂(x)∩L| oriented cycle edges have both endpoints in X: each successor outside X of an X vertex has original distance two from x. We will insert several vertices by subdividing distinct original eligible edges. Fewer than or equal to h+e−1 insertions will be needed.

A remaining zero-W triple t occurs only in the second selection case and sees a double-mask port J. No exclusive remote can see J, so |Sⱼ|≤b+h. Its degree gives aⱼ≥k−(b+h)−2−(e−1)=k−b−h−e−1. The vertex t has all aⱼ of these W-neighbors and three anchors at distance two, so |D₂(t)∩L|≤k−aⱼ−3. Also |N(t)∩L|≥k−e−(h−1). Thus the number of eligible cycle edges is at least

    aⱼ−e−h+4 ≥ k−b−2h−2e+3 ≥ h+e−1,

where b≤12, e≤6 and k≥7h+84.

For a remaining triple t with 1≤a=|N(t)∩W|<2h choose a neighboring w∈W. Among the |W|−a W-nonneighbors of t, at most h+2 miss w. The others have distance two from t, as do three anchors. Hence |D₂(t)∩L|≤e+a+h−1, while |N(t)∩L|≥k−a−e−(h−1). Eligible cycle edges number at least

    k−2a−2e−2h+2 ≥ k−6h−2e+4 ≥ h+e−1.

At least two anchor classes have a single private. Reserve its private P in one such class i and an exclusive remote q from that class, so P is q's only middle neighbor. Existence follows from |Uᵢ|≥c−2(k−2)+h≥h+3. Each unreserved exceptional port J with aⱼ<2(h+e−1) has at least k−aⱼ−e−h−1 neighbors on L. Every L-cycle successor outside its L-neighborhood of a member of that neighborhood lies in Hⱼ∖Sⱼ. Its eligible-edge count is therefore at least

    k−2aⱼ−2e−h+1 ≥ k−5h−6e+7 ≥ h+e−1.

Assign distinct eligible original edges greedily to the three classes just considered, and subdivide. The expanded cycle opens at q even if some inserted triple lies immediately next to q; deleting any one incident cycle edge gives a spanning path beginning at q.

Each unassigned triple has ≥2h W-neighbors. Give each a disjoint pair of its W-neighbors, which is possible greedily even if all h require pairs. Next give each remaining unreserved exceptional port its own disjoint pair of W-neighbors: each has ≥2(h+e−1) choices and before the last pair at most 2h+2(e−2) are used. Replace each assigned pair by its oriented W–assigned vertex–W block and retain unused W vertices as singleton blocks. There are B₀≥k−h−2e+1≥4h+10 blocks. As each W vertex misses at most h+2 other W vertices, the undirected graph joining pairs of blocks that can be concatenated in either order with these fixed orientations has degree at least B₀−1−2(h+2)≥B₀/2. Dirac gives a Hamilton cycle of blocks. Opening it produces a path through W and all vertices assigned to its pairs whose last vertex belongs to W.

The three anchors and z have a spanning path ending at i, starting at an anchor: use the edge between the other anchors followed by z,i when that edge exists; otherwise start at the anchor outside an edge incident to i, then traverse z and that edge ending at i. Append this path to the W traversal, then continue through P and q onto the opened expanded L-cycle. Every joining edge is original and all vertices are covered. This proves the theorem.
