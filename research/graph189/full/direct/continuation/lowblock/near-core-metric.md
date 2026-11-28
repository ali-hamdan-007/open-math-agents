# The exact three-edge obstruction at internal degree k−1

Fix a Graph 189 instance with second degree k. Let H be induced, with minimum internal degree at least k−1; all its vertices are assumed high in G. Suppose every exterior v has t(v)=|N_G(v)∩V(H)|≤k−1. All ambient distances two transfer exactly to H. Indeed the intersection bound for nonadjacent H-neighbors a,b of an exterior v is now |N_H(a)∩N_H(b)|≥2(k−1)−(t(v)+k−2)=k−t(v)≥1.

If an ambient distance-three pair a,b does not have a three-edge H-path, every shortest original path through outsiders must use two of them, say a,v,w,b. A path with at most one outsider could use the distance-two transfer. Write t(v)≤t(w) by reversing if necessary. If a had any H-neighbor also touching w, we could replace v and then apply the distance-two shortcut. Hence their two H-neighbor sets are disjoint. Both lie in (B₂^G(v)∩H)∖{a}, so

    d_H(a)+t(w)≤t(v)+k−1.

This forces equal contact counts t(v)=t(w), d_H(a)=k−1, and equality of the ball bound. Applying the reversed argument forces d_H(b)=k−1 as well. Each of v,w is saturated and all its k even witnesses lie in H at distance two, since the ball bound would otherwise be smaller. Thus both are adjacent to every other vertex in their component of G−H: along a path from either to a nonneighbor in the component, some second-distance vertex would occur. Each has eccentricity at most three in G as its second layer exhausts the cap. In particular the possible new even pairs in H are supported exclusively on pairs of internally degree-(k−1) endpoints across an induced a,v,w,b with a saturated edge vw universal inside its outside component.

If H has at most one vertex of degree k−1, all original odd distances among H points therefore transfer exactly: these were one or three since all H points were originally high. H is connected, because distinct components would be pairwise at original distance four, and each component has at least k+1 vertices. For the latter, any component that contains an internally high vertex has order at least k+1 and a component without one could consist only of the single internally deficient vertex, which has degree k−1. We assume k≥3 here. Hence H has even cap ≤k and second-smallest degree at least k, and is qualifying.

More generally, if no exterior edge has the forced equality pattern, the same odd distances transfer without limiting the number of internal degree-(k−1) vertices. If in addition every remaining originally saturated vertex is at positive even distance from some outsider, the cap on H improves to k−1. Each H component has order ≥k. Different components would still be at original distance four. In this case they are also impossible: fix a point a in one and k vertices of a second. These already exhaust its original even cap, so a was saturated and cannot have an additional even witness outside H. Thus H is connected and qualifies with second degree at least k−1.

## A persistent total-degree deficit during k-core peeling

In a minimum-order counterexample seed the peeling cascade by any degree-k vertex when the minimum is tied, or by the unique low vertex when there is one. Iteratively delete one remaining vertex of degree below k in any permitted order. Before h+2 vertices have been deleted, with h=ceil(k/2), every nonempty deleted prefix S leaves

    sum over x outside S of max(0,k−d_(G−S)(x)) ≥ 2.

The first singleton deletion is isometric by the minimum-vertex theorem. If its deficit sum were at most one the remaining graph would qualify and its spanning path would violate the universal gap. For every later prefix, all survivors are originally high, and each previously peeled vertex has at most k−1 surviving contacts. The seed also has at most k−1: a low seed did initially, and for a tied degree-k seed the second vertex removed had to be its neighbor. A total deficit at most one would make the preceding near-core theorem applicable. The remaining graph would qualify and its spanning path again misses at most h+1 vertices. This proves the deficit bound, in all removal orders and without any saturation hypothesis.
