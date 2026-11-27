# A uniform order range for Conjecture 189

**Theorem.** Let G be a finite connected graph satisfying the even-distance hypothesis of Conjecture 189. Write δ for its minimum degree and k for its second-smallest degree. Then G has a Hamilton path whenever

    n ≤ max{3k−4, δ+2k+2}.

The proofs for n≤δ+2k and n=δ+2k+1 appear in order-bound.md and boundary.md. The result below supplies the next order and an additional range for graphs with one lower-degree vertex. We use the saturated independent-set theorem of saturated-independent.md, for sets of size k+1 whose pairs are all at distance two. As previously, Easwar–Johari handle graphs that are not 2-connected. If k≤2 and n is in the stated range, their known small-order bound n≤2k+3 suffices except possibly k=2,n=8,δ=2, which is treated separately below.

## The uniform part

Suppose n≤3k−4. If δ=k this follows from order-bound.md, so suppose δ<k and call the unique low vertex z. We may assume G is 2-connected. Put J=G−z. Any independent set of size k+1 in J has all pairs at distance two in G, because two vertices at distance at least three would have disjoint neighborhoods, each of size at least k and disjoint from the set, requiring at least 3k+1 vertices. The saturated independent-set theorem settles that case. Thus α(J)≤k.

The argument in the final part of boundary.md now applies without an assumption on the gap k−δ: the minimum degree in J is at least k−1, and its order is at most 3k−5. If J is 2-connected, the Bauer–Veldman–Morgana–Schmeichel circumference theorem gives a spanning or almost-spanning cycle. For a unique vertex w omitted by a longest cycle, w together with the successors of its neighbors is independent in J, so d_J(w)≤k−1 and w is a neighbor of z. Both possibilities give a Hamilton path in G. If J has a cut vertex, deleting it leaves exactly two components, each of size at least k−1 and at most 2k−5. They are Hamilton-connected because their internal minimum degree is at least k−2. Distinct attachments to z and the cut vertex give a Hamilton cycle as in boundary.md.

## The cone at n=δ+2k+2

It remains to handle this exact order, as the previous orders up to δ+2k+1 were settled by the earlier files. If h=k−δ≥6 then n≤3k−4, already covered. Assume h≤5. Put H=G plus one universal vertex, with N=|H|. The independent-pair count gives α(G)≤k+2: an independent (k+3)-set with a pair at distance at least three would require at least δ+2k+3 vertices, while if all its pairs were at distance two the cap would fail.

We prove H is 1-tough. If it were not, some set S of s≥2 original vertices would leave t≥s+2 components in G−S after removal (t>1 and ≥2-connectivity of G are used here). Representatives from different components are independent, so s≤k. Each component has size at least k−s+1, except that a component consisting of the unique low vertex might fall below this by up to h.

* For 2≤s≤k−2 we have n≥s+(s+2)(k−s+1)−h. The quadratic before subtracting h is at least 4k−2. This exceeds 3k+2 for k≥5. The only remaining possibility is k=4, s=2, with equality throughout the count. There are four components. At least three consist of exactly three high vertices, since all but at most one component have lower bound three. In each such component every vertex sees both members of S to reach degree four. One of them then has all six vertices in two other such components at distance two, contradiction.
* For s=k−1 (so k≥3), every component has size at least two except possibly a singleton low vertex. If t≥k+2 this needs at least 2k+3 vertices, and available order is 2k+3−h. Equality would require h=0 and a low singleton, impossible. Thus t=k+1. Let e be 1 if there is a singleton and 0 otherwise. When e=1 we have h≥1. The excess over the minimum sizes of these t components is 1−h+e≤1. There is at most one component of size greater than two. There are at least two pairs for which both vertices have degree at least k: when e=0, either all vertices are high with one size-three component (h=0) or all components are pairs with at most one pair containing the low vertex; when e=1 at most one component besides the singleton fails to be a pair. Each fully high pair sees every member of S. From a vertex of one such pair, at least one vertex of each of the k other components is at distance two because each component has some neighbor in S. The second fully high pair contributes two such vertices. This exceeds the cap.
* For s=k there are t=k+2 components, and at most 2k+2 vertices outside S. If no singleton has degree at least k, these components require at least 2k+3 vertices. Thus a high singleton exists; it sees every member of S, and hence a representative of all k+1 other components at distance two, again impossible.

These arguments cover k=2 as well: only s=k is possible. This deals in particular with the previously mentioned n=8,δ=k=2. The k=1 range is already within n≤2k+3.

## Applying the circumference criterion

Every independent triple of H has degree sum at least δ+2k+3=N. If H has no independent triple use Chvátal–Erdős; otherwise Hoa's 1-tough circumference bound from boundary.md applies. For h≤2 use α(H)≤k+2. It yields a circumference at least min{N,N−h/3}, strictly exceeding N−1. Hence H is Hamiltonian.

For 3≤h≤5 there is a unique low vertex z. If G−z has an independent set of size k+1, its members must be pairwise at distance two in G, because n=3k+2−h<3k+1. The saturated set theorem settles that case. Otherwise α(G−z)≤k, so α(H)=α(G)≤k+1. Hoa's bound now gives at least min{N,N+(3−h)/3}, again strictly above N−1. Removing the universal vertex from the resulting Hamilton cycle proves traceability.
