# An upper order bound at arbitrary minimum-cut size

Let G be a qualifying graph with s=κ(G)≥5 and k>6(s−1). Then G is traceable whenever

    n ≥ (s+3/2)k + 2s+2.

In particular if k≥2s²+6s+2, every nontraceable qualifying graph would have each minimum-degree vertex in some minimum vertex cut. This second consequence uses the stronger minimum-order bridge of root/universal-minimum-order.md and includes every fixed s≥5 for all sufficiently large k.

Take a hypothetical counterexample in the displayed order range. Every minimum s-cut S leaves precisely two components (global/minimum-cut-two-sides.md). Write A for the smaller high side, X≤Y for their high populations, and H=X+Y≥(s+3/2)k+s+1. From XY≤kX+sk², x=X/k≤(1+sqrt(1+4s))/2 and H/k≤x+1+s/x. At x=6/5 this upper bound is 11/5+5s/6<s+3/2 at s≥5. At the other endpoint it is 1+sqrt(1+4s)<s+3/2. Convexity thus gives X<6k/5 and Y>sk. The singleton-low A case directly gives n≤(s+1)k+s+1 by distance parity at its full anchor set.

Every label i has a high A contact. Otherwise the edge from i to its sole A contact z has all its common neighbors in S. The edge-order theorem gives at least ceil((n−3k−2)/(k+1))≥s−1, so i touches every other anchor. Indeed n≥(s+3/2)k+2s+2 implies n−3k−2>(s−2)(k+1). Since |B|>sk, no first step in A shortens two anchor distances, by the s-root even cover. A high A contact at another label therefore must touch i. At least one such high contact exists: if the connected side contains more than the single low vertex, having only one attachment vertex would contradict connectivity.

If all high A ports are private (each touches just one label), then the private-port sum in private-five-cut.md, valid in every arity, gives Y≤sk+P_A/s+1. To recall, the high private representatives' internal neighborhoods leave at most P_A+s anchor slots for high B nonports. Their even sets cover each B port and every B nonport at each of its missing distance-two labels, giving P_B+sD_B−Σ|J(y)|≤sk. Now P_B≤sk and P_A≤X. This would bound H≤sk+(1+1/s)X+1<sk+(36/25)k+1. A high A nonport forces this very case: its high-pair distance to an opposite nonport is four; if it has depth ≥3 all opposite high vertices must be ports at four. Otherwise a cover of its nearest labels by ≤s−1 A ports, together with this nonport, covers all high B at even distance. Since Y>sk, every label is nearest and no A port spans two labels. This excludes a high A nonport.

All high A members are thus ports. Any two of their supports T,U satisfy |U−T|≤1. The port on T covers all high B ports meeting T and all high nonports having no member of T at distance two. The anchors in T pay other nonports; if U covers two unused labels, at most s−|T|−1 A representatives cover every other B port. This would give Y≤sk.

Let the high A supports have common core C, c=|C|, and d=s−c residual labels. For d≥2 the elementary set-family result in private-five-cut.md gives only residual singletons (optionally empty), or all residual co-singletons (optionally full). The representative counts in five-cut-large-degree.md hold for this general s. Explicitly, split high B ports by whether they hit C (counts P_C and P_D), and let G count the high B nonports with no distance-two label in C; at most ck others remain. For residual singleton representatives,
   
    dP_C+P_D+dG−Q≤dk,   Q≤X+d(c+1),    P_D≤dk,

where Q sums the residual distance-two labels over G. The bound on Q holds since each residual representative has ≥k−c−1 high vertices in its closed internal neighborhood, and each high A vertex touches at most one residual label. Hence Y≤sk+X/d+c+1. The c=0 case was excluded above. For c>0, X≤k by an opposite port at any common label, so H≤sk+(3/2)k+s−1. For the co-singleton family, if G1,G0 count nonports in G having one or zero exact-two labels,

    dP_C+(d−1)P_D+G1+dG0≤dk,   2G≤dk+G1+2G0.

For d≥3 this gives Y≤sk. For d=2 with no full support use the singleton case. If a full high port exists, it sees every B port; then the same co-singleton inequalities give Y≤sk+P_D/2≤sk+k/2. Here c>0 because s≥5, giving H≤(s+3/2)k. These contradictions prove that on every minimum cut the smaller side's high vertices share at least s−1 labels, and a high port touches all s labels because every label has a high contact.

This full high port sees all B ports and high B depth-three vertices with one even quota. Every label has a singleton-nearest high B depth-two vertex, since otherwise the other s−1 anchor quotas cover all remaining high B vertices, giving Y≤sk. Choose a private B representative at each label, obtained from a geodesic of the corresponding nonport. If X≥k−s+1 there is a high such representative v at a common label i; it sees all X high A vertices at distance two. Otherwise the degree of a high A vertex forces X=k−s, with a low z in A, all high A vertices complete in A and to S, and all B vertices high. If z has any incident label i choose its corresponding v: it sees all k−s+1 A vertices. If z has none, its distance to B is two plus the depth, whereas a full high root's distance is one plus the depth, giving |B|≤2k.

The connected internal neighborhood W=N_B[v] now has ambient boundary at most s, equal to the one possible neighbor i of v outside W plus at most s−1 further boundary vertices at distance two outside A. At most k high B ports exist and at most k of its nonports belong to W, since those are at exact distance two from i. After removing the boundary the opposite group therefore has more than (s−2)k−s>6k/5 high vertices. Consequently ∂W is a minimum cut, W is its smaller side, and v is a high vertex with only one neighbor on this cut. This contradicts the already proved common-support lower bound s−1. The order assertion follows.

If any minimum-degree vertex belongs to no minimum cut, the previously proved bridge gives n≥(s+2)(k−s+1)−1=(s+2)k−s²−s+1. At k≥2s²+6s+2 this is at least (s+3/2)k+2s+2, proving the stated corollary.
