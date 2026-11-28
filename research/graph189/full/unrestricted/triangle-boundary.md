# Triangle transversals at k = 3t+2

Let X meet every triangle, t=|X|≥1 and k=3t+2 the second-smallest ambient degree. Under the full Graph 189 even-distance hypothesis G has a spanning path. The earlier strict-inequality proof already handles k≥3t+3. Together the bounds say that a counterexample needs a triangle transversal of size at least ceil((k−1)/3), and at least ceil((k−1)/9) disjoint triangles (as well as at least one).

Write H=G−X, E_b=N_H(b) for high b with d_G(b)≥k. As in the previous proof, |E_b|≥k−t and two intersecting such sets have union of size at most k+1. If their intersection relation is transitive, the earlier odd-cycle argument makes H bipartite. At k=3t+2 the previous *sharper integer threshold* for a bipartite deletion gives traceability, including disconnected H.

If transitivity fails, write A,F,B for three high-index neighborhoods, with outer sets A,B disjoint and both meeting the middle set F. Set r=k−t=2t+2. Then

    r ≤ |F| ≤ |F∖A|+|F∖B| ≤ (k+1−|A|)+(k+1−|B|) ≤ 2(t+1)=r.

Every inequality is tight. In particular |A|=|B|=|F|=r, F is contained in Ω=A∪B, and |A∪F|=|B∪F|=k+1. The three index vertices each have *all* of X as neighbors, and each has ambient degree exactly k. Denote the middle index by b.

For any a∈A∩F, its closed even-distance set is exactly A∪F. The other members of that union are at distance two through one of the two high indices: the induced graph H is triangle-free. The union uses its entire ambient parity allowance. For a∈B∩F the corresponding set is B∪F. In particular every a∈F has eccentricity at most three (distance at least four gives a distance-four vertex on a geodesic) and every a is adjacent to every x∈X: otherwise the two-edge route a,b,x supplies an extra even witness.

Every vertex q at distance three from b belongs to Ω. A shortest path b,a,p,q starting in F gives d(a,q)=2 and the conclusion. Otherwise it starts b,x,p,q with x∈X. Then p∉F, since otherwise q is within distance two of b. The two sets A∪F, B∪F intersect in exactly F, so p misses at least one of them. Choose a in the corresponding A∩F or B∩F. The path a,x,p gives d(a,p)≤2; since p is outside its complete even set, d(a,p)=1. Now d(a,q)=2, so q is again in Ω.

Since b has an F-neighbor of eccentricity at most three, b has eccentricity at most four. Its neighbors number k, all positive even layers together have size at most k, and its third layer has size at most |Ω∖F|=2t+2. Hence

    n ≤ 1+2k+2t+2 ≤ 3k+2.

The independently reviewed bounded-order theorem gives a spanning path. This boundary argument needs the full even-distance cap to turn saturated distance-two counts into actual eccentricity information. It makes no bipartiteness claim in the nontransitive case.
