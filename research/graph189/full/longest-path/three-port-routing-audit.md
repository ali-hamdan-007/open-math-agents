# Routing the three ports of an omitted component

Assume the minimum-degree-three residual in degree-three-audit.md. Let the omitted component H have order k−1 and exactly three attachment positions p,q,r, each with at least two contacts in H. Write B=H∪{p,q,r}. Every vertex of H has all its neighbors in B and has degree at least k. It therefore misses at most one other member of B. Every H vertex sees at least two ports. The low vertex z sees at most one port, since any two port neighborhoods cover H and |H∩D₂(z)|≤4 while |H|≥5.

## A prescribed span of the three ports

For any two prescribed ports p,q there is a spanning path in B from p to q. Add a marker adjacent to p,q. The augmented order is k+3. If r has at least three neighbors in B, each port has augmented degree at least three, since p,q already have two H-neighbors. Every missing edge inside H or between H and the ports can be added by ordinary cycle closure at threshold k+3. Each port now sees all k−1 H vertices, so each missing port-port edge qualifies as well, since 2(k−1)≥k+3. A Hamilton cycle through the marker exists in the completed graph. Reversing closure and deleting the marker gives the asserted path in B.

If r has only two B-neighbors, they are distinct vertices a,b of H. Every vertex of H other than a,b misses r and sees all its remaining possible B-neighbors. Pick such an x and use the path p,x,a,r,b followed by all remaining H vertices in any order and then q. There is at least one remaining H vertex. All transitions are original edges.

## Disconnected remainder

For k≥10, the graph is traceable if G−B is disconnected. Every component of G−B contains a high vertex: if it were just z, its degree would be at most one because z sees at most one port. All external neighbors of a high vertex in its component lie in the three ports, so the component has order at least k−2. The total order of G−B is at most 2k. Therefore there are exactly two such components, each of order at most k+2. The all-high component has internal minimum degree at least k−3. Deleting z from the other leaves internal minimum degree at least k−4 and order at most k+1. Both high subgraphs are Hamilton-connected by the endpoint-marker degree condition 2δ≥order+1, valid for k≥10.

Some high vertex in the component containing z has a port neighbor, as otherwise deleting z separates its high vertices from the rest of G. Starting at such a high vertex, span its high subgraph to a different internal neighbor of z and append z. This choice is possible because z has at least two internal neighbors. The all-high component has contacts of at least two different ports by 2-connectivity, so can start its spanning path at a contact of a different port. Join the two paths through the full three-port block with the prescribed port endpoints.

## Remainder with a cut vertex

For k≥12, the graph is traceable if the connected remainder C=G−B has a cut vertex w. Each component of C−w contains a high vertex; a singleton z could see only w and at most one port. Each part therefore has order at least k−3, and their total order is at most 2k−1. There are exactly two parts, each of order at most k+2. An all-high part has internal minimum degree at least k−4 and is Hamilton-connected. If the other part contains z, deleting z there leaves internal minimum degree at least k−5 on at most k+1 vertices, again Hamilton-connected for k≥12.

In an all-high part there is a contact of w and a contact of some port p. The first follows from connectedness of C and the second from connectedness of G−w. Some such two contacts must be distinct: if their union were one vertex, its deletion would disconnect the remaining vertices of this part. Span this part between the contacts. If the other part is all high, span it starting at any contact of w. If it contains z and w sees z, start at z, enter an internal high neighbor and span the high subgraph from there. If w misses z, start at a high contact of w, finish the high subgraph at a distinct neighbor of z and append z. There are at least two internal z-neighbors in this last case, and at least one when w sees z. Start the global path at a port other than p, traverse all of B ending at p, traverse the first part, use w, and follow the spanning path of the second part.

Codex (GPT-6) for @ali-hamdan-007.
