# Traceability above half the second-smallest degree

**Theorem.** Let G be a finite simple connected graph in which every vertex has at most k other vertices at positive even distance, where k is the second-smallest degree. If κ(G)>k/2, G has a spanning path. This proof treats k≥4. The previously proved k≤3 and minimum-degree-at-most-two cases supply the smaller parameters. The condition allows a unique exceptional low vertex of degree below k.

Put t=floor(k/2), h=ceil(k/2), δ=δ(G) and n=|G|. The independently kernel-checked quadratic order theorem gives

    n≤1+δ+k+floor((k+1)²/4)≤ U,
    U=t²+5t+1 (k=2t),  U=t²+6t+4 (k=2t+1).

Call a vertex high if its ambient degree is at least k. Assume G is nontraceable and fix a longest path P. Every endpoint of P has all its neighbors in P, and at least one endpoint is high, so |P|≥k+1.

## The internal degrees outside P

For a vertex x of a component C of G−P let A_x be its set of contact indices on P, a_x=|A_x|, q_x=deg_C(x). These contacts avoid endpoints and consecutive indices. Their two shifts supply a_x+r_x distinct distance-two witnesses, where r_x is the number of step-two runs of contacts. Thus no high singleton can lie outside P. If the only omitted vertex were low z, contacts two positions apart would also be impossible: exchange z for their intervening vertex, obtaining another longest path which omits a high singleton. This would yield 2δ distinct shift witnesses, contrary to 2δ≥2κ>k. It therefore suffices to contradict one omitted component C containing a high member.

Every high x in C has a high neighbor in C. If it had no neighbor there, the shift bound would contradict a_x≥k. If its only C-neighbor were the unique low vertex z, then a_x≥k−1≥2, hence a_x=k−1 and r_x=1, saturating its two-step cap. Any other C-neighbor of z would be an additional witness. Thus C={x,z}. Any contact of z outside A_x is another witness, disjoint from the shifts by the forbidden insertion of the edge xz between consecutive positions. Hence A_z⊆A_x. Every member of the unique A_x run has another member two positions away. A z contact in A_x permits replacing their midpoint by the adjacent x,z, strictly lengthening P. Thus A_z is empty and z has degree one, contrary to κ≥t+1.

For adjacent high members x,y of C, a y-contact at position one or two away from an x-contact would lengthen P by insertion or by replacing the midpoint. If r_x<a_x, a shared contact can therefore occur only in a singleton run of A_x, giving |A_x∩A_y|≤r_x−1. The distance-two witnesses from x include its shifted positions, the contacts A_y∖A_x, and N_C(y)∖(N_C(x)∪{x}). These sets are disjoint and the last has size at least q_y−q_x. Consequently k≥a_x+a_y+1+q_y−q_x≥a_x+k+1−q_x in the nonsingleton-run case. If a_x≤floor(k/2), the degree bound immediately gives q_x≥h. Otherwise 2a_x>k forces r_x<a_x, and the last calculation gives q_x≥a_x+1≥h. Every high C vertex thus has q_x≥h. In particular |C|≥h+1.

## No long exterior cycle

A cycle of length d≥2h in C has t pairwise vertex-disjoint connectors to P by Menger's theorem. Deleting fewer than t vertices leaves both sets nonempty and the graph connected. Trim each connector to have its interior disjoint from the two sets. Their marks on P and contacts on the cycle are distinct. Each outer tail of P contains at least d nonmarks, by replacing the tail through the corresponding connector and around the whole cycle. Each of the t−1 gaps contains at least ceil(d/2)+1 nonmarks, using the longer cycle arc between contacts. Counting these intervals, the marks, and the disjoint cycle gives

    n≥3d+t+(t−1)(ceil(d/2)+1).

At d≥2h this is at least t²+7t−1 for even k and t²+8t+4 for odd k. Both exceed U since t≥2.

## Routes in a block

Consider a two-connected block B in which all vertices other than possibly a distinguished w have internal degree at least h. Fan's circumference theorem says that if each pair at distance two has an endpoint of degree at least c/2, a two-connected graph has a cycle of length at least c for 3≤c≤|B|. Apply it with c=min(|B|,2h). The long-cycle exclusion gives b=|B|≤2h−1 and a Hamilton cycle in B.

To prescribe distinct endpoints, add a marker adjacent precisely to them. Bondy–Chvátal cycle closure adds all missing edges between vertices other than w, their original degree sum being at least 2h≥b+1. Thus the endpoint question can be decided with all of B∖{w} a clique. Every w-to-port pair has a spanning path: leave w through a neighbor other than the specified port and traverse the clique. For two other ports, insert w between two of its neighbors in the clique path. This works unless w has exactly two neighbors and these are exactly both ports. Even in this one possible exceptional pair a length-maximizing arc on the Hamilton cycle gives a path through at least ceil(b/2)+1 vertices. Whenever b=h+1 the whole block is already a clique, since every high internal-degree vertex is universal.

If C itself is two-connected, apply the preceding argument with w its possible low vertex (any w suffices if all vertices are high). Match t+1 distinct members of C to t+1 distinct marks on P. A contrary vertex cover of size at most t of the C–P edges would separate surviving vertices of C and P, by König's theorem, since both sets have more than t vertices; this contradicts κ≥t+1. The two outer tails can each be replaced through all b vertices of C using a Hamilton cycle, as can each interior gap except at most one, since the matched contacts are distinct. If b=h+1 the clique routes every gap, hence n≥t+1+(t+3)(h+1). If b≥h+2, allow the exceptional gap zero vertices and obtain n≥t+1+(t+2)(h+2). At even k these lower bounds are respectively t²+5t+4 and t²+5t+5, and at odd k they are t²+6t+7 and t²+6t+7. They all exceed U.

If C has a cut vertex, at least two blocks are leaves of its block-cut tree. Choose a leaf B in which all noncut vertices are high, possible since at most one vertex is low. All such vertices have degree at least h within B. A bridge leaf is impossible because its noncut vertex would have internal degree one. Let w be the unique cut vertex of C in B. Then h+1≤b≤2h−1 and all the block routes already proved apply. Writing R=C∖B, match t distinct members of B∖{w} to distinct P marks. Otherwise a vertex cover of size less than t, together with w, separates the remaining block interior from P. There are b−1≥h≥t interior vertices, so some survive.

Read the t marks along P. All interior gaps have at least b vertices except potentially one, whose deficit is at most s=floor(b/2)−1. Take s=0 for b=h+1. Each outer tail has at least b+1 vertices, using a spanning matched-port-to-w route through B followed by a neighbor outside B. Counting C as well gives

    n≥t+(t+2)b+|R|+2−s.

If R contains a high vertex, |R|≥h since its C-neighborhood lies in R∪{w}. For b=h+1 the lower bound is at least t+(t+2)(h+1)+h+2, i.e. t²+5t+4 or t²+6t+7. For b≥h+2 use s≤h−2, giving at least t+(t+2)(h+2)+4, strictly larger in either parity. The global order bound forces R={z} for the unique low vertex z, with zw its sole edge into C.

Now z sees q_w−1 other internal neighbors of w at distance two, in addition to its a_z+r_z shifted positions and the contacts A_w∖A_z. The last set is disjoint from the shifts by the forbidden consecutive insertion of zw. As q_w≥h, a_z=δ−1≥t, and r_z≥1, we obtain

    k ≥ q_w−1+a_z+r_z+|A_w∖A_z| ≥ h−1+t+1 = k.

Therefore q_w=h, a_z=t≥2, r_z=1, and A_w⊆A_z. Every member of the single A_z run is two positions away from another. Any w attachment would allow replacing the midpoint by w,z. Thus A_w is empty and deg_G(w)=h<k, impossible. This exhausts all exterior components and proves traceability.

The root order theorem is `Graph189OrderBound.order_le` in the preceding research checkpoint. The external graph inputs are Menger's and König's theorems, the circumference theorem of G.-H. Fan (1984), and the Bondy–Chvátal closure theorem (1976). Explicit Fan statement: https://www.sciencedirect.com/science/article/pii/S0012365X04002729. Original Fan paper: https://www.sciencedirect.com/science/article/pii/0095895684900546. Closure: https://www.sciencedirect.com/science/article/pii/0012365X76900789.
