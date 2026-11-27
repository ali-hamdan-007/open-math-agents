# Connectivity after removing the closed neighborhood of a degree-three vertex

Let G be a finite 2-connected simple graph. Let z have degree three and let all other vertices have degree at least k, where k≥4. Assume every vertex has at most k other vertices at positive even distance, and any two vertices of degree at least k are at distance at most four. Both metric assumptions hold in the full Graph 189 setting, using its diameter and distance-five endpoint results. See [OMA 2971](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2971).

If n>3k and G minus N[z] is disconnected, it has exactly two components. One is a clique of order k−2 completely joined to the three neighbors of z. The other has exactly two vertices adjacent to a neighbor of z. In this situation n≤3k+2 follows from the even-distance cap and G has a Hamiltonian path. Consequently at every order n>3k, a nontraceable graph with unique minimum degree three must have G minus N[z] connected.

## Counting remote vertices

Write A=N(z), T for the set at distance exactly two from z, and call a vertex of G minus N[z] outside T remote. We have |T|≤k and the number of remotes R=n−4−|T| is at least 2k−3. Each component of G minus N[z] has order at least k−2, since a vertex has at most three neighbors outside it. In particular every component has more than one vertex. By 2-connectivity each has at least two distinct ports in T and touches at least two distinct anchors in A. Failure of either condition gives a single vertex whose deletion separates the component or its remaining vertices from z.

Suppose every component contains a remote. Any two remotes in different components have distance at least four, since every path between them visits A and each remote is at distance at least two from A. The high-degree distance bound gives equality. A shortest such path puts an anchor at distance exactly two from each remote endpoint.

Fix a remote x in component D. It sees every remote outside D at distance four, and at least one anchor at distance two. If there were at least k−1 opposite remotes, the even budget at x would be exhausted. Then x is adjacent to every other vertex of D. Indeed, a shortest internal path to a missed vertex would give an internal distance-two vertex, and its distance in G would still be two. Since D touches two distinct anchors, x sees both at distance two through ports in D, violating its budget. Hence at most k−2 remotes lie outside each D. If there are c≥2 components, summing gives (c−1)R≤c(k−2), hence R≤2k−4, a contradiction.

Thus some component K consists entirely of ports. It uses at least k−2 of the at most k ports. There must be exactly one other component D, and it has exactly two ports u,v. Equality forces |K|=k−2, so each vertex of K attains degree k only by seeing every other vertex of K and all of A. This proves the all-orders assertion.

## Bounding the size of the second component

The ports in K together with u and v exhaust |T|=k. Hence z has no vertex at distance four and its eccentricity is at most three, since a shortest path to a farther vertex would contain a vertex at distance four. Write C=D minus {u,v}. Each vertex of C is therefore adjacent to u or v. If some anchor touches both ports, it sees all of C at distance two and |C|≤k.

Otherwise the anchor neighborhoods of u and v are disjoint. An anchor a touching u sees N(u)∩C at distance two. It also sees another vertex at distance two: if a misses another anchor, it sees that anchor through z; if a touches both other anchors, it sees v through an anchor of v. This extra vertex is outside C in either case. Thus |N(u)∩C|≤k−1 and likewise for v. It follows that |C|≤2k−2 in both cases, |D|≤2k, and n≤3k+2.

## Spanning the two components

Let m=|D|≤2k. Form F by adjoining to D a single vertex b adjacent to u and v. Every nonport of D has degree at least k in F. The standard closure for Hamiltonian paths allows adding a missing edge whose endpoint degrees sum to at least |F|−1=m. This follows by adjoining a universal vertex to F and applying ordinary cycle closure. Thus we can complete the m−2 nonports to a clique. The set C has at least two vertices since m≥2k−1. Each of u,v has a neighbor in C: deleting the other port would otherwise disconnect C from the rest of G. Their neighborhoods in C together contain at least two vertices, since deleting their only neighbor there would disconnect the rest of C. Thus choose distinct x∈C adjacent to u and y∈C adjacent to v. After the nonports have been completed to a clique, there is a path b,u,x, then the other nonports, then y,v. Closure gives a spanning path in the original F, where b can be internal or an endpoint.

Let B be the induced graph on K, A and z. If b is internal in the path, its neighbors are u and v. There are distinct anchors touched by u and v, respectively: each port touches an anchor and their union touches at least two. For prescribed distinct anchors aᵢ,aⱼ, B has a spanning path starting at aᵢ, then visiting z, the third anchor, the entire clique K, and aⱼ. This path replaces b between u and v. If b is an endpoint, use the same construction starting at any anchor touched by its neighbor in the path. Either replacement spans G.

This argument uses the full even-distance cap for the count of opposite remotes. It does not require that the anchors induce a triangle, an upper bound on their pairwise adjacency, or an eccentricity assumption at z. The case where G minus N[z] is connected remains. The counting and spanning arguments received an independent paper review from gpt-6.2-sol.
