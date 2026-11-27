# A minimum separator that leaves more than its size in components

Let G be a finite 2-connected graph satisfying Graph 189's distance-two cap k, where k is the second-smallest degree. Let S be a cardinality-minimum vertex cut, write s=|S|=κ(G), and suppose G−S has t≥s+1 components. Every x∈S has a neighbor in every component: otherwise deleting S minus x would leave an isolated component and contradict cut-minimality.

Suppose first that each component contains a vertex of degree at least k. There is some x∈S that contacts a high vertex in every component. All except at most one component have only high vertices; and, in a nonsingleton component containing the unique low vertex, that low vertex cannot be the only point of contact to S since its removal would disconnect G. Put a_i=|N(x)∩C_i| and A=Σa_i. A neighbor of x in C_i has all A−a_i x-contacts outside C_i at distance two, so (t−1)A≤tk. A high neighbor of x in C_i has at least k−s+1 members of its closed neighborhood inside C_i. At most a_i are x-neighbors, so the remaining members witness distance two from x. Summing yields A≥t(k−s+1)−k. Since s≤δ≤k, the latter lower bound increases with t and tk/(t−1) decreases. Taking t=s+1 gives

    (s²−s−1)k ≤ s(s²−1).

For s≥3 this forces k≤s+1, since s(s²−1)/(s²−s−1)=s+s²/(s²−s−1)<s+2.

If instead a component is the singleton low vertex z, it is adjacent to every member of S by cut-minimality. Thus the union of all the high components' S-contact sets has size at most k by the cap at z. Fix x∈S. There are t−1≥s other components, and from a high x-neighbor in each one the same disjoint distance-two count gives k≥(t−1)(k−s+1)−Σa_i. Restricting the sum to the high components gives Σa_i≤k. Therefore

    (s−2)k ≤ s(s−1).

This implies k≤s+1 for s≥5, and k≤6 for s=3 or 4. These inequalities require a minimum separator (or, more generally, that each component contacts every member of S). They do not assert the same conclusion for an arbitrary failing toughness cut.

## Classification for s≥3

The preceding arithmetic resolves all cardinality-minimum separators of this kind. For s≥3, the only possibility is k=s, t=s+1, and every component of G−S a singleton complete to S. This graph contains a spanning complete bipartite graph with parts of sizes s and s+1, hence a spanning path.

If there is a low-only singleton z, its degree is s and k>s. Every other component has at least k−s+1≥2 vertices and therefore at least two distinct attachment vertices (2-connectivity). The vertex z sees each such attachment at distance two, so k≥2s. Together with (s−2)k≤s(s−1) this forces s≤3. With s=3 these inequalities force k=6. Every high component then has at least k−s+1=4 vertices and at least three distinct attachment vertices: if it had at most two, deleting its attachments would disconnect an internal vertex from G, contrary to κ(G)=3. There are at least three high components, so z has at least nine positive even-distance witnesses, contradiction.

Otherwise k=s or s+1 by the previous bound and s≤δ≤k. Use the high-valid anchor x found above, with one high contact u_i in each component. Write h_i=|N(u_i)∩S|. At least k+1−h_i vertices of its closed neighborhood belong to its component, so at least k+1−h_i−a_i of those are found at distance two from x. Summation refines the earlier inequality to

    Σ_i(s−h_i) ≤ k+A−t(k+1−s).

If k=s+1, t=s+1: for t≥s+2 the earlier lower bound gives A≥2t−k≥s+3, whereas A≤tk/(t−1)≤s+2. Thus A≤s+2 and the displayed defect sum is at most one. In particular there is a contact adjacent to all S. Every component has at least k−s+1=2 vertices and at least two distinct attachment vertices. The all-S contact in one component has all the attachment vertices of every other component at distance two, at least 2s>k, a contradiction.

If k=s, t=s+1 since t−1≤k, and A=t by the upper bound. The displayed defect sum is at most s. At least one of the s+1 chosen contacts therefore sees every vertex of S. Its allowance k=s leaves room for just one attachment in each other component. These other components are singletons since G is 2-connected. Each such singleton sees all S by the minimum-cut property, so its distance-two bound also forces the original component to have only one attachment and to be a singleton. This proves the classification.
