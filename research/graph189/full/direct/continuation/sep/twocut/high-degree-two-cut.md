# Connectivity two for k≥26

Let G satisfy Graph 189 with second-smallest degree k≥26 and vertex connectivity two. Write h=ceil(k/2). A vertex of degree at least k is high. There is at most one low vertex, every vertex has at most k other vertices at positive even distance, and high pairs have distance at most four. The following paper proof covers this entire range. It uses the original global path-gap theorem, Fan's circumference theorem, and a linked-set order estimate.

## Order and choice of cut

A counterexample has minimum degree δ≥3 by the degree-two theorem. The order-through-3k+2 theorem and the edge-order bound then imply that every edge belongs to a triangle. Also n≥4k−9. To prove this, take a minimum-degree vertex z.

* If deleting z leaves a Hamiltonian path, the rooted matching order at parameter 3 gives n≥4k−5, since its matching parameter is at least deg(z)≥3.
* If the deletion is nontraceable and z belongs to no minimum cut, completing z to a universal vertex lifts connectivity to at least three. Use the minimum-completion linked-witness theorem at parameter 3 and degree bound k to obtain n≥4k−5.
* If z lies on a minimum cut, the anchor-degree estimate gives δ≥k−1. Critical connectivity provides a vertex u whose universal completion has connectivity at least three. The high-minimum path gap and independent-exterior bound supply an edge outside each longest deletion path at u. The linked-set construction at parameter 3 applies using 9≤k+2, 8≤δ, and k+6≤2δ. Its cycle order bound with degree bound δ is n≥4(δ−1)−1≥4k−9.

The linked-set order theorem is in @koolkao's accepted [Ma–Ning–Zhao formalization](https://github.com/lefttosolve2/open-math-agents/pull/7971). The local assembly of the order bound is in Graph189PairOrder.lean and awaits the pinned check.

Choose a two-cut with a component A of minimum size among components of all two-cuts. Call the anchors p,q. Each component contacts both anchors by 2-connectivity and has at least two vertices by δ≥3. There are exactly two components. Otherwise some anchor has high contacts x₁,x₂,x₃ in three components. Only one component could contain a low vertex, and that vertex cannot be its sole contact with the cut since elsewhere it contains a high vertex. Let Pᵢ count contacts in those components for the chosen anchor. Summing the even quotas at xᵢ gives 2ΣPᵢ≤3k. Each xᵢ has a closed internal neighborhood of at least k−1 vertices, all at distance one or two from the anchor. The anchor's even quota gives 3(k−1)≤ΣPᵢ+k, impossible.

Write B for the other component and a,b for the side orders, so k−1≤a≤b. A port touches at least one anchor, a common port touches both, and a private port touches exactly one. Write l_A,l_B for the low counts in A,B, with sum at most one.

## Metric bounds

Suppose a vertex u in A touches every label at distance two from a high nonport x in A. Vertices of B sharing an anchor with u count at distance two from u. All remaining high B vertices have distance four from x. Indeed, a shortest route of length at most three would go through an anchor at distance two from x and adjacent to its destination. By 2-connectivity a nonempty fourth layer has at least two second-layer vertices, so at most k−2 vertices occur in the second group. The u-row counts at most k in the first, and adding at most one low proves b≤2k−1.

Suppose a high p-private e in A has distance at least three from q and A contains a noncontact of p. An internal path from e to that noncontact supplies a second-layer A witness for p. The vertex e misses all q-contacts of A, hence has its own internal second-layer witness. For high B vertices outside the second layer from p, d(e,y) equals two if y touches p and four otherwise. In the latter case both anchor routes cost at least four, and the high-pair bound supplies the reverse inequality. The two rows therefore count at most 2k−2 high vertices of B, and b≤2k−1.

Finally a high nonport opposite at least k−1 high vertices must be at distance two from an anchor. Otherwise all those opposite vertices are at distance four and its second layer adds at least two witnesses.

## Side paths and balanced orders

In a component D adjoin an apex adjacent to its ports. This graph is 2-connected. Deleting the apex leaves connected D, and after deleting any vertex of D, each remaining component has a port because the original graph after deletion stays connected. Each high vertex has degree at least k−1. Add the apex–low edge temporarily if there is a low vertex in D and that edge is absent. The two possible vertices of degree below k−1 are adjacent, so Fan's theorem yields a cycle of order at least min(|D|+1,2k−2). If it contains the apex, drop the apex and start at a genuine contact, since only one apex edge could be temporary. Otherwise reach the cycle by a shortest path from the apex in the original apex graph and open the cycle at the entry. Dropping the apex gives a path from a genuine port covering at least min(|D|,2k−3) vertices.

If b≤2k−1 and pq is an edge, join these paths through one anchor if their contacts match, or through pq otherwise. They miss at most five vertices. When pq is absent, take the apex path on the side containing the low vertex, or either side if neither does. The opposite side D is wholly high. The selected anchor has at least two contacts in D, by the triangle on a contact edge and the absence of pq.

If D is internally 2-connected, adjoin an apex only at those selected-anchor contacts. The new graph stays 2-connected and every D vertex keeps degree at least k−1, losing at most its other anchor edge. The Fan argument gives at least min(|D|,2k−3) vertices from a contact of the selected anchor.

If D has a cut vertex, its minimum internal degree is at least k−2. Each leaf block has at least k−2 noncut vertices, so there are exactly two leaves by |D|≤2k−1. An intermediate block with a noncut vertex would have at least k−1 vertices disjoint from the two leaf interiors, impossible. The block-cut tree is a path, and intermediate blocks must be bridges. Two consecutive bridges would give an internal degree-two vertex. Each leaf's core of noncut vertices has order at most k and minimum degree at least k−3, hence is Hamilton-connected by Ore's criterion. From a prescribed port in a core, span the core to a different neighbor of its articulation. Such a neighbor exists since the leaf block is 2-connected. Append the articulation and join to the analogous path in the other leaf across the shared articulation or bridge. This spans D.

Both anchors have a contact in some leaf interior. Otherwise, if both cores miss p, their vertices each lose at most one anchor neighbor, so both cores have at least k−1 vertices. The order bound forces equality. Each core vertex then has at most k−1 internal neighbors, so all 2k−2 of them touch q. An opposite q-contact counts all of them at distance two, impossible. Thus the wholly high side matches either anchor. Joining the two paths misses at most five vertices, contradicting the global gap of h+2.

## Large B and no common port in A

Suppose now b≥2k. If A contains a high nonport, the first metric bound implies that it is at distance two from both anchors and that A has no common port. Otherwise a contact of a sole nearest label, or a common port, would cover all nearest labels.

Assume A is common-free. Each private type has a high representative by the edge-triangle condition. Every high port of A is at distance two from its missing anchor by the second metric bound. As a high A vertex loses at most one anchor neighbor, a≥k. Then A has at least k−1 high vertices and each high nonport of B is at distance two from an anchor.

Let w and v count high B nonports at distance two from both anchors and from exactly one, respectively. Write t for the common B port count, l≤l_B for the number of low B nonports, and r for the high A nonport count. The two private representatives in A give

    b ≤ 2k−2 + w + l − t.

Each sees its missing anchor, all opposite ports of its own type including common ones, and the singly nearest nonports whose nearest label is its missing anchor. The latter distance equals four because both anchor routes cost at least four and one realizes four. Common ports count in both rows. The two anchor rows independently give

    a − l_A + r + v + 2w ≤ 2k.

Since b≥2k, we have w≥2−l. Thus a≤2k−2 if l_A=0 and a≤2k−3 otherwise. Combining the two inequalities with a+b=n−2 gives

    b ≤ 6k−2 − n + l_A − r − v + 2l − 2t.

The B-apex path misses at most b−2k+3 vertices. Whichever anchor it uses, A supplies a path from one of its contacts, missing at most l_A. Use Dirac's cycle theorem in A if it is wholly high, or in A−z if z is low, since the remaining internal minimum degree is at least k−2. If only z touches the chosen anchor, start at z and enter the cycle at an internal neighbor. Counting the unused anchor, the path misses at most b−2k+4+l_A≤11+2l_A+2l≤13, using n≥4k−9, within the gap allowance.

## A common port and both private types

Now A has a common port and no high nonport. If both private types exist, choose a high representative of each if possible. The second metric bound forces these representatives to be at distance two from their missing anchors. If a type has only the low vertex, every internal neighbor of this vertex is high and touches its missing anchor. It too has distance two to that anchor. At least one private is high, so a≥k and every high B nonport has a nearest anchor at distance two. The two representative rows give b≤2k−2+w+l_B as before.

Let c be the common A port count. Its common port sees every B port at distance two, so there are at most k. The anchor rows count at least a−c−l_A+v+2w, while v+w≥b−k−l_B. Hence n+w≤3k+c+l_A+l_B+2. Each anchor has at most k A contacts, as seen by an opposite contact, so a≤2k−c+l_A and n≤4k−c+w+l_A+l_B. The two inequalities give 2n≤7k+4, contradicting n≥4k−9 for k≥26.

## Recutting a shallow side that lacks a private type

Let A have no q-private port. Every high A vertex touches p. An opposite p-contact sees all A p-contacts at distance two, so their number is at most k and a≤k+1. If there are k such contacts, every B p-contact is internally universal because an internal nonneighbor in connected B supplies an additional second-layer witness. Then p sees every noncontact in B at distance two, and an A p-contact bounds B p-contacts by k. This gives b≤2k and contradicts the lower order.

We may choose p so that there are exactly k−1 A contacts of p. If the present choice has fewer, a=k−1 includes the low vertex z. Each high vertex is common and universal in A to attain degree k. If z is a port, choose one of its anchors as p. If it is a nonport, take any high x in A. Their distances to y in B are respectively d(x,y)=1+min(d(p,y),d(q,y)) and d(z,y)=2+min(d(p,y),d(q,y)), by the separator shortest-path formula. One is positive even, giving b≤2k.

Any B p-contact now spends k−1 even places across the cut. If one is common, consider the torso on B,p,q with pq added. It is 2-connected by compressing visits to A in paths after any single deletion. Distances from the common vertex agree with ambient distances: compression cannot increase length, while any shortest torso path from that vertex avoids the added edge because the vertex already touches both labels. The common vertex thus has at most one second-layer vertex, and no third layer since such a layer would give a cut of size at most one. The p-row now gives b≤2k+1. If pq is present, or if a B edge joins opposite private types, some B p-private contact sees q at distance two. It is internally universal since q takes its remaining even place, and b≤2k. These bounds contradict n≥4k−9 because a≤k+1.

We may assume pq is absent and the B private types are anticomplete. Choose a high B p-contact y, available via a triangle on a contact edge. Put U=N_B[y]. The internal distance-two layer of y consists of one vertex w, since otherwise y would be internally universal or would exceed its quota. Let W=B−(U∪{w}). It is nonempty, or the p-row gives b≤2k+1. There are no U–W edges, no p-contacts in W, and no q-contacts in U. Each of the latter two possibilities would give y an additional second-layer witness. Every high W vertex is at distance three from y by the saturated even row and high-pair bound. The penultimate vertex along a geodesic must be w, since every other vertex at distance two from y lies in A and has no edge to B. Thus w touches every high W vertex.

Deleting q,w separates W from A, so |W|≥a by the minimum choice of A. Let U₀=N_B(w)∩U, nonempty by the internal two-step route to w. Each u in U₀ sees all high W at distance two. The vertex u must miss p, since otherwise the k−1 A contacts of p and the at least a−1≥k−2 high W vertices together exceed its cap. Instead u sees p itself at distance two through y, so |W_high|≤k−1. If A contains a high private vertex then a≥k, and A must contain the low vertex because all its high vertices are among its k−1 contacts of p. Then W is wholly high, a contradiction.

All high A vertices are therefore common, numbering at least k−2. Some W vertex touches q or deleting w alone would disconnect G. If the sole q-contact in W were low, say z, the triangle on qz could only use w. Indeed z misses A,U,p. If w touches q, each u in U₀ sees p,q and at least k−2 high W vertices at distance two, exhausting its row and forbidding wz. Thus there is a high q-contact f in W.

The vertex f touches w and sees all high A vertices and all U₀ at distance two. Thus |U₀|≤2 and f has at most 2−|U₀| distance-four witnesses. Any high x in U−U₀ has distance three or four from f. It cannot be at distance two via q since U lacks q-contacts, via w since x misses w, or via W since there are no U–W edges. A length-three route must start through w. A first step into W or to q cannot reach x within two further steps, since A,W,q,w have no edge to x and pq is absent. Therefore w counts all such distance-three vertices at distance two. Allowing |U₀| exceptional vertices and at most 2−|U₀| at distance four from f gives |U_high|≤k+2. Hence b≤(k+2)+(k−1)+1+1=2k+3 and n≤3k+6<4k−9. This finishes the proof.

Graph189TwoAnchorSeparation.lean and Graph189PositiveEvenCut.lean verify the first metric bound and the second-layer separator. Graph189FarPrivatePort.lean and Graph189PairOrder.lean contain the new metric and lower-order statements and await compilation. The combined proof is at paper level and has no official checker verdict.
