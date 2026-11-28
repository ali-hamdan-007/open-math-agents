# Cycle of saturated above-degree vertices under a local degree condition

Let G be a 2-connected finite simple graph of order n>3k+2, where k is its second-smallest degree. Assume every vertex has at most k other vertices at positive even distance. For every induced wedge u–w–v assume

$$
   d(w)+k \le d(u)+d(v)+1.
$$

Let D consist of the vertices w with d(w)>k and |N₂(w)|=k, joining two such vertices precisely when their distance in G is two. If D is a forest, then G has a Hamilton cycle. The proof permits an arbitrary degree sequence satisfying the displayed local condition. Without the lower bound on order, the earlier paper theorem for n≤3k+2 gives traceability. At large order this strengthens the {k,k+1} result.

By wedge-cover.md the graph is L₁. Consider endpoints u,v with sole common neighbor w. As in unique-center-cycle.md, Q={u,v}, so the union of the three open neighborhoods has size d(u)+d(v)+1. It must omit some vertex of B₂(w) by the parity covering lemma, and |B₂(w)|≤1+d(w)+k≤d(u)+d(v)+2. Equality holds everywhere. Thus d(w)=d(u)+d(v)+1−k, the second layer at w has size k, eccentricity(w)≤3, and the set M of missed vertices is a singleton {b}. Since at least one endpoint has degree at least k and the other has degree at least the minimum δ, the center has degree at least δ+1. In particular the unique vertex z of degree below k, if present, is never the center of a wedge whose endpoints have just one common neighbor.

The set T of vertices equidistant at common odd distance at least three from u,w,v has size at least n−3k−1≥2, by the parity lemma. All are at distance three from w and have only b as a neighbor in B₂(w). Choose t∈T of degree at least k. Let J=N(w)∩N(b). If the unique low vertex z constituted all of J, then w,b would have sole common neighbor z, which was just proved impossible. Hence choose a∈J of degree at least k. Since N(a)⊆B₂(w), the sole common neighbor of a,t is b. Applying the equality for such wedge centers gives d(b)=d(a)+d(t)+1−k≥k+1 and |N₂(b)|=k. Thus b belongs to D. Its new singleton missed vertex c differs from w because a is adjacent to w. Iteration using high-degree choices for a,t now supplies an arbitrarily long immediately nonbacktracking walk in D (the initial w may be dropped). A finite forest admits no such walks. Therefore every distance-two pair has two common neighbors. Theorem 7(a) of Asratian, Broersma, van den Heuvel and Veldman now yields a Hamilton cycle, since the exceptional graphs have n=2k+1.

Primary source https://ris.utwente.nl/ws/files/6633608/Asratian96on.pdf
