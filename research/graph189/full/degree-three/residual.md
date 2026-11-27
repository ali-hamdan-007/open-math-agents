# Nine rooted incidence templates when all three covering pairs fail

Let G be a finite simple connected graph of order n>3k, with integer k≥9, and let z be a degree-three vertex of eccentricity at most three. Assume every other vertex has degree at least k and every vertex has at most k vertices at distance exactly two. Write A=N(z) for the three anchors, B=N₂(z), and C=N₃(z). Suppose no two anchors cover B, meaning their combined neighborhoods omit at least one member of B for each pair. Each anchor then has at least one private B vertex adjacent to that anchor only. Number the anchors with bits 1,2,4, and represent each B vertex by its nonempty anchor-neighborhood mask. Put d=k−|B|. A given anchor of anchor-degree a has at most 1+a−d misses in B. Choose one private B vertex for each anchor and delete these three from the miss budgets. Each anchor now has residual budget at most a−1−d. In particular there is no isolated anchor, and at least two anchor edges are needed. Each listed template is a necessary incidence pattern, not an existence assertion. The omitted vertices in B have mask 7.

| Anchor graph | d | All non-universal masks, up to an anchor automorphism |
|---|---:|---|
| Path centered at anchor 1 | 0 | 1,2,4 |
| Path centered at anchor 1 | 0 | 1,2,4,6 |
| Triangle | 1 | 1,2,4 |
| Triangle | 0 | 1,2,4 |
| Triangle | 0 | 1,1,2,4 |
| Triangle | 0 | 1,2,3,4 |
| Triangle | 0 | 1,1,2,4,6 |
| Triangle | 0 | 1,2,3,4,5 |
| Triangle | 0 | 1,2,3,4,5,6 |

Indeed, in a path each leaf has residual zero so d=0, and the center can miss at most one more vertex. With a triangle d≤1. If d=1 there are no residual misses; if d=0 the three anchors each have one. Extra double masks consume one of those seats each, and an extra private consumes two. Distinct extra masks must consume pairwise disjoint sets of seats, giving exactly the six triangle patterns in the latter case.

Let V_i be the C vertices visible at distance two to anchor i, and U the C vertices visible from exactly one anchor. Each anchor already has at least two nonremote distance-two partners. In a triangle these include the two other private vertices, and in a path the center has the other two private vertices while each leaf has the opposite anchor and the center's private middle vertex. Hence sum_i |V_i|≤3k−6, which implies

|U|≥2|C|−Σ_i |V_i|≥2(2k−3+d)−(3k−6)≥k+2d.

Also |C|≤3k−6 so n≤4k−2−d. Each member of U has all B neighbors in its exclusive anchor's class of private middle vertices. A common B vertex adjacent to every private middle vertex has all U and z at distance two, contrary to the cap. Thus every common B vertex misses at least one private. More strongly, for each common w the collection of its missed private vertices must contain all B neighbors of at least |U|−k+1 members of U, since those with any B neighbor adjacent to w already give distance-two partners in addition to z. This is a necessary bound; the nine residual templates are still unresolved at general k.

For a specific next reduction, let U_i be the remotes visible only to anchor i, T the remotes visible to all three, and f_i the number of nonremote distance-two partners of i. Write c=|C| and u_i=|U_i|. For distinct i,j,h one has

u_i=c−|V_j∪V_h|≥c−2k+f_j+f_h+|T|.

In the seven templates having exactly one private B per anchor, call it p_i. If a common middle vertex w is adjacent to p_i and p_j, the cap at w gives u_i+u_j≤k−1, accounting also for z. Consequently if 2(c−2k+4+|T|)≥k, every common w is adjacent to at most one of the three p_i. Since w has at least k neighbors and sees no remote outside T, it can miss at most 2−d+|N(w)∩T| members of B. The remaining question on this branch is whether the three incidences to the p_i can meet these two per-w restrictions and their own distance-two budgets. The most rigid starting case is d=1 and T empty: each w can miss at most one p_i, so the displayed inequality rules this case out. Equivalently when d=1 and T is empty, the order satisfies |C|<(5k−8)/2. These statements concern the seven singleton-private templates; the two templates with one doubled private class need separate handling.
