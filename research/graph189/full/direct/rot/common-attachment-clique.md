# Larger exterior cliques with a common attachment set

Assume the hypotheses of `even-exterior.md`. Let P be a longest nonspanning path and suppose a component C outside P is a clique of size m≥2 all of whose members have the very same set A of neighbors on P. Write a=|A|. Two-connectivity gives a≥2. The vertices of C have equal degree m−1+a, necessarily at least the second-smallest degree k. Therefore m≥k−a+1. All gaps and tails between the marks A have at least m nonmark vertices by a path through the clique. For a fixed x∈C its 2a distinct brackets B are all at distance two, so k≥2a≥4 and m≥a+1≥3. Put X=N(A)−(C∪A). This is precisely the second distance layer from x, with |X|≤k. The only neighbors of x outside C belong to A.

## A high endpoint can avoid every mark

There is a path using exactly V(P) with a high endpoint that has no neighbor in A. To prove this, let R be the set of all endpoints occurring on paths using exactly these vertices. Every u∈R admits such a path to a high opposite endpoint: if the opposite endpoint is low, its degree at least two permits rotating it through a neighbor other than its successor. It cannot be adjacent to the far endpoint, since the resulting cycle on V(P) could be opened to annex a vertex outside P. All neighbors of every endpoint belong to V(P). Rotating the high opposite endpoint gives at least k distinct possible endpoints other than u, one for each neighbor pivot, including the trivial rotation. Thus |R|≥k+1.

No attainable endpoint belongs to A or C. If every high endpoint neighbors A then all high members of R lie in X and at most one remaining member is low. The preceding inequality implies |R|=k+1, |X|=k and R comprises X and the unique low vertex outside X. Every high member e of R has exactly k neighbors: on any realization of e as a left endpoint every neighbor produces a different new left endpoint, belonging to R minus the fixed right endpoint. This predecessor-of-pivot map is therefore onto that k-element set. For each mark, its immediate predecessor on the realization lies in X⊂R and is not the right endpoint. Surjectivity forces the mark to be adjacent to e. It follows that all of X is complete to A. These k vertices exhaust the even-distance budget of x, so every other vertex outside C∪A∪X lies at distance three from x and touches X. All of them are at distance two from each mark, giving at most k such vertices. Hence |P|≤a+2k. On the other hand |P|≥a+(a+1)m and

    (a+1)(k−a+1)−2k = (a−1)(k−a−1)>0.

This contradicts m≥k−a+1, proving the endpoint assertion without any diameter hypothesis.

## A necessary metric or degree defect

Set r=k−2a and e=m−1+a−k. Assume m≥4 and that every vertex is at distance at most four from x. A sufficient condition for this eccentricity restriction is κ(G)>r, since |L₄(x)|≤r and a nonempty fifth layer would be separated by the fourth layer. Then

    1+a e ≤ (a−1) floor(r/2).                                      (1)

In particular a common-contact clique of any order is excluded whenever e≥floor(r/2) and x has eccentricity at most four. Under the same degree inequality, an actual such exterior forces an x-distance-four vertex separator of size at most r, with a nonempty fifth layer beyond it. When r≤1, two-connectivity supplies the eccentricity assumption automatically. The elementary m=3 possibility gives a=2,k=4 and was already excluded in `even-exterior.md`.

Use a path on V(P) with a high endpoint avoiding A, supplied above. Let B be its 2a brackets and W the vertices outside C∪A∪B. The 2a outward representatives W₀ are distinct by m≥4. Let s_P be the sum of all gap and tail excesses above m. Thus |W−W₀|≥(a+1)m−4a+s_P. For a mark v use the three sets from `even-exterior.md`: its nonneighbors among the other marks, brackets of v or its neighboring marks that it misses, and representatives of its bracket neighbors S_v. Write U_v for brackets of v and adjacent marks, d_v for its number of neighbors in A, D=Σd_v, E=Σ|S_v−U_v|. Before correction these sets supply a+1+d_v+|S_v−U_v| vertices at distance two. The first two sets are valid; a representative w_b can fail only if v is adjacent to it, which implies w_b∈X−B.

Every member of W at distance three from x is at distance two from a mark, by taking a geodesic from x through A and X. Consequently the uncovered vertices of W−W₀ all lie in (X−B)∪L₄(x). This set has size at most r and also contains the distinct exceptional representatives (those that fail for any v). Bound the number of failed *incidences* as follows. For a bracket b belonging to mark u, a failed incidence at v=u charges its representative w_b. For v≠u with v nonadjacent to u, charge b∈S_v−U_v to E. For v adjacent to u, charge the ordered pair (v,u) to D once. A second charge to that pair requires both brackets of u to have exceptional representatives. There are at most floor(r/2) such u and at most a−1 new ordered losses at each. Together with uncovered W−W₀ vertices, all corrections total at most r+D+E+(a−1)floor(r/2). Summing the corrected three-set count gives

    |W−W₀| ≤ a(k−a−1)+r+(a−1)floor(r/2).

Comparing the two estimates on |W−W₀| and using m=a+r+1+e gives

    s_P ≤ a−1−(a+1)e+(a−1)floor(r/2).

The high endpoint avoiding A has k≤deg≤m−1+s_P by the endpoint chord bound. Substitution gives (1).

The existing registered R1 results (lemmas `diameter_le_five` and `five_endpoints` at line 505 of `WrittenOnTheWallII.GraphConjecture189.conjecture189.R1.lean`) give diameter at most five and at least one endpoint below k for every distance-five pair. Here x is high, so its fifth layer has size at most one. In the proof with no eccentricity restriction, the additional uncovered W−W₀ vertices can only lie in L₅(x). Accordingly (1) becomes

    1+a e ≤ (a−1)floor(r/2)+|L₅(x)|,      |L₅(x)|≤1.

If floor(r/2)≥1 and e≥floor(r/2), the right-hand side is at most (a−1)floor(r/2)+1, strictly smaller than 1+a e. If r≤1, two-connectivity already excludes a fifth layer. Thus e≥floor(r/2) excludes a uniform-contact exterior clique with no diameter or eccentricity restriction.
