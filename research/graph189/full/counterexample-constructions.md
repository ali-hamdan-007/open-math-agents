# Asratian–Granholm gadgets and the full Graph 189 cap

Asratian and Granholm's [Proposition 4.1 and Theorem 4.2](https://arxiv.org/pdf/2107.07037) work with the radius-two cap |N₂(v)|≤k in connected k-regular graphs. Graph 189 caps the **sum over all positive even distances**, not just N₂, by the second-smallest degree σ. The zero-distance vertex appears on both sides of the original cap via the offset of one.

## Proposition 4.1, parallel branches

Use two cliques A and B with groups A_i and B_i, respectively. The i-th branch consists of terminals w_i,w_i′, two disjoint cliques U_i∪V_i and U_i′∪V_i′, and a matching between V_i and V_i′. The terminal w_i sees A_i and U_i. The other terminal sees B_i and U_i′. In the paper |A_i|=|B_i|=|V_i|=|V_i′|=k_i and |U_i|=|U_i′|=k−k_i, with three branches and sum k_i=k.

Each branch admits a spanning path from w_i to w_i′: traverse U_i and V_i with a matched vertex last, cross its matching edge, then traverse the opposite clique starting with that partner and ending in U_i′. Alternating branch directions lets us join these paths through consecutive groups in the appropriate hub clique. The representatives of each group are distinct since the groups partition the hubs, and the remaining hub vertices can be inserted in those clique portions. Thus the graphs are traceable for every number m≥2 of branches and arbitrary positive group sizes, with equal positive matching-side sizes inside each branch. Odd m forbids a spanning **cycle** because each branch must cross both terminal interfaces exactly once in such a cycle, so the cycle would switch hubs an odd number of times.

For the regular parameters, let t=k_i and generalize to m≥2 branches. The positive even shells are:

| Location of the vertex in branch i | Distance 2 | Distance 4 | Distance 6 | Distance 8 | Sum |
| --- | ---: | ---: | ---: | ---: | ---: |
| Hub group A_i | k−t+m−1 | k | 1+(m−2)k+t | k−t | (m+1)k−t+m |
| Terminal w_i | k | (m−1)k | k | m−1 | (m+1)k+m−1 |
| U_i | 2t | m | 2(k−t) | (m−2)k+t | mk+t+m |
| V_i | k | k | (m−2)k+t+m−1 | k−t | (m+1)k+m−1 |

Distances follow by walking from a source toward one or both terminals, then using the hub clique edges to change branches. For example, from A_i, distance 2 reaches U_i and the other left terminals, distance 4 reaches V_i′ and all V_j for j≠i, distance 6 reaches w_i′ and all U_j′ for j≠i, and distance 8 reaches the other groups of the right hub. Any route between different branches must pass through a hub. The two terminals and the matching are the only entrances or crossings between consecutive layers of a branch.

The maximum even sum is (m+1)k+m−1, which exceeds k even for the original k=6 example. The maximum second neighborhood is k whenever all k_i≥m−1.

Even arbitrary positive block size tuning fails. Pick a branch i whose right clique has degree d_i=|U_i′∪V_i′|≥σ. Such a branch always exists because at most one vertex has degree below σ, and the right clique degrees are uniform within each clique. A vertex v∈V_i sees its matched partner at distance one, every other vertex of the opposite clique at distance two through its partner, and w_i at distance two through U_i. These total d_i at distance two. Every vertex in the nonempty B_i has exact distance four via the partner, U_i′ and w_i′. Thus v violates the full cap even if the graph is irregular.

## Theorem 4.2, replacement of a cubic bipartite source

For a source edge e=xy with x on the U side and y on the V side, insert one connector w_e adjacent to every vertex of U_x and to its own nonempty portal subset of V_y. U_x and V_y are cliques; the three portal subsets of V_y partition V_y. The paper uses |U_x|=4 and two portals per edge, so |V_y|=6 and the entire image is 6-regular.

From a vertex of U_x, exactly six vertices lie at distance two, the assigned portal pairs for its three incident edges. Exactly six further connectors lie at distance four, two at the far end of each incident y. Indeed one must cross from the first connector through the V clique to reach a different connector; the two involved portal subsets are disjoint and each step is necessary. Thus every image fails the full cap by at least six.

Positive size tuning to arbitrary irregular block sizes still fails. For an x-block of degree |U_x|+2≥σ, choose an incident edge xy and a vertex v in its assigned subset of V_y. At distance two from v are all of U_x and the other two y-connectors, giving |U_x|+2 vertices. Every portal in V_y′ assigned to some other edge xy′ is at exact distance four, via w_xy, U_x and w_xy′. No path shorter than four can connect different V cliques because every such transit uses two connectors and a U clique. A suitable x exists because the source has at least three x-blocks and at most one vertex of the resulting graph can have degree below σ.

## Traceability of the cubic source and its image

A spanning path in the image projects to a connected spanning subgraph of the source. Mark a connector crossed if its interior path incidence enters from U and exits to V, or vice versa. Assign every uncrossed connector to the label of its sole adjacent clique along the path. The successive clique labels then trace a walk on the source graph that uses precisely the crossed edges and repeats no edge. Every source vertex appears. Its crossed degree is even except possibly at two terminal source labels. Since the source is cubic and the crossed graph connects every label, nonterminal degrees are exactly two, and two different terminal degrees are each one or three.

A connected graph of this form has a spanning path. With no odd vertices it is a cycle. With two odd vertices, contract the degree-two chains. If both are leaves it is a path. If one has degree one and one has degree three, a cycle is attached to a path at the degree-three vertex. If both have degree three, the two vertices in the contracted multigraph have either three parallel edges, or one connecting edge and one loop each. Thus the original shape is a theta or two cycles joined by a path. For a theta, traverse the interiors of two arms at the ends of the spanning path and the third arm between the branch vertices. For a cycle attached to a path or two cycles joined by a path, remove one cycle edge at each junction. These operations retain every vertex.

Conversely, a spanning path of the source lifts to a spanning path of the published image. Follow the path through the used connectors. At a V clique its chosen entrance and exit lie in disjoint nonempty portal subsets, so all V vertices can be covered by a clique path between them. At each U clique use its four vertices and insert the unused connectors between distinct successive vertices. There are at most two unused connectors at a source path endpoint and at most one at an interior source vertex. Every unused connector is handled by its unique U endpoint.

For an explicit certified-nontraceable source, start with planar K₂,₂ with a matching of two edges doubled. Replace each of its six edges by a separate copy of the cube with an edge deleted, attaching the two deficient vertices to the original endpoints. The deficient cube vertices belong to opposite classes, so bipartiteness is preserved. Each edge gadget is planar with its two deficient vertices on a common face, so the replacement preserves planarity. Each gadget is 2-connected because the cube stays 2-connected after deleting any one vertex, so removing one remaining edge cannot then disconnect it. The doubled K₂,₂ is itself 2-connected, and the gadgets are joined along its edges, preserving 2-connectivity. Removing the four original anchors leaves six components, more than the five a spanning path could meet. The source is cubic and has 52 vertices. Its image is another nontraceable graph, but it fails the full even cap.

## Reproduce the metric calculations

Run `python3 check_constructions.py`. It constructs the actual graphs and computes shortest-path distances by BFS for every vertex. It checks a spanning path for the parallel-branch constructions, their exact layer formulas, cubicity and absence of cut vertices in the source example, and the six-components certificate upon removing the four anchor vertices. The image has 338 vertices, degree 6, diameter 30, max N₂=6 and a positive even count between 137 and 194. In particular, the distinction between the published radius-two condition and the full Graph 189 condition is substantial.
