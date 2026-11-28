# Opening the equality case of the linked-set order bound

Work over finite simple graphs. Let G have a distinguished vertex w. Let K be the graph obtained by making w universal and leaving all other edges unchanged. Suppose every vertex other than w has degree at least d in G. Fix 2≤l≤d. Suppose K has connectivity at least l and minimum degree at least d. Suppose some longest cycle C of K has a linked set D in its exterior in the precise sense of Graph189LinkedExterior.Linked: D has at least l+1 vertices and every pair of distinct members admits a path within D on at least l vertices. Under the order equality

    n = (l+1)(d−l+2)−1,

the original graph G has a Hamiltonian path.

## Equality in the two counting inequalities

Use the ambient graph K until the final paragraph. Let H be the component of K−C containing D, and c the number of cycle vertices. Use the disjoint-path extraction and notation of the accepted OMA.BondyK.linked_contra proof. For q disjoint links from D to C under its route length hypothesis, cyclically order their endpoints t_i and let u_i be their immediate successors. The accepted succ_deg lemma gives

    sum_i deg(u_i) + 2q + |H| ≤ n+q².

If every D–C separator had at least l+1 vertices, take q=l+1 by Menger. Since all the successors have degree at least d, substitution of the order equality yields |H|≤l, contradicting D⊆H and |D|≥l+1. There is therefore a separator S of size exactly l; fewer vertices cannot separate D and C by connectivity and their cardinalities. The l disjoint links supply l distinct cyclic endpoints t_i. Choose v∈D outside S. As in the accepted proof, every cyclic neighbor of v occurs among the l endpoints. Equivalently vert_deg gives deg(v)+1≤|H|+l. Applying succ_deg at q=l gives |H|≤d−l+1. The minimum-degree bound at v gives the reverse inequality. Consequently

    |H| = d−l+1,   deg(v)=d,   deg(u_i)=d for every i.

Only |H|−1 neighbors of v can be internal, hence v has exactly l neighbors on C, equal to all the chosen endpoints. Each lies in S since its one-edge link from v must meet S. Thus S comprises precisely the l cyclic endpoints. As H is connected and disjoint from S, an edge from any x∈H to a cyclic vertex y outside S would extend an internal v–x path to a D–C path avoiding S. Hence every member x of H has at most |H|−1 neighbors within H and l possible neighbors outside. These account for exactly d vertices. All must be neighbors of x, so H is a clique complete to S, with no other external neighbors. Each x∈H has K-degree exactly d.

## Spanning and opening the actual cycle

Let m=|H|. For each consecutive pair of anchors around C, replace the arc joining them by a path visiting all m vertices of H. The anchors are distinct because l≥2. The other arc and the replacement form a cycle. Maximality of C implies that at least m internal vertices lay in each replaced arc. Therefore c≥l(m+1). Since c+m≤n and n=l(m+1)+m, equality holds: C and H partition V.

The universal vertex w belongs to C because otherwise inserting it into any cycle edge increases the length. Since it is adjacent to all of H, w∈S. Its successor has K-degree d, as proved above. Every H vertex also has K-degree d. Each of these vertices is distinct from w and has degree at least d in G. Their edges to w are consequently genuine: if an edge to w were new, their K-degree would exceed their G-degree by one. Take a Hamiltonian path of the clique H, continue from its final vertex to w, and traverse C from w to its predecessor along the successor edge. Every retained cycle edge other than the first avoids w. The result is a Hamiltonian path in G.

## The k=7, n=23 parent case

The previously checked degree-two theorem handles minimum degree two. Assume the minimum degree is at least three. A Hamiltonian minimum deletion is impossible in a counterexample: the checked strict matched-path bound at index four would give n≥24. If the minimum degree is below seven, the checked tight-pair result implies the minimum vertex w lies in no minimum two-cut. If connectivity is at least three, taking the minimum w also works directly. In either case K has connectivity at least three and minimum degree at least seven, and the nontraceable deletion supplies an exterior cycle of length at least four at every longest K-cycle, hence a linked set at index three.

It remains possible that the minimum equals seven and connectivity is two. The critical-connectivity theorem supplies a free vertex w whose completion has connectivity at least three, and all original vertices have degree at least seven. The rounded arbitrary-completion argument in Graph189AllIndexThree gives the four-cycle in the exterior in this case as well. Apply the equality theorem with d=7 and l=3. Thus the entire k=7,n=23 case is resolved on paper. Together with the preceding strict index-three result this covers every moderate order at k≥7.

The pinned Lean 4.33.1 kernel compiled Graph189BondyEquality.lean with warnings treated as errors. The declarations linked_layout and equality_layout_of_linked have exactly the axioms propext, Classical.choice and Quot.sound. The latter theorem recovers the saturated exterior clique, all common anchors and all successor degrees from an actual longest cycle and a linked set in its actual exterior. The cyclic gap comparison and Hamiltonian-path transfer are separately tracked formal obligations. No official parent verdict is claimed.
