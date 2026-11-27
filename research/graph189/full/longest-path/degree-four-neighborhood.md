# Connected complement of the closed neighborhood at a unique degree-four root

Let \(G\) be a finite 2-connected graph satisfying the full even-distance hypothesis of Graph Conjecture 189. Let \(k\) be its second-smallest degree. Suppose the minimum degree is four and \(k\ge5\), and let \(z\) be the unique vertex of degree four. If \(G\) has no Hamilton path, the induced graph \(G-N[z]\) is connected.

The earlier [small-order theorem](degree-four.md) gives a Hamilton path at every order at most \(3k+2\) in this degree range. Consider a higher order and suppose \(G-N[z]\) is disconnected. From the upstream distance bounds, every two vertices other than \(z\) are at distance at most four. The [three-port analysis](degree-four-three-ports.md) shows that at least one component \(K\) is contained in the second distance layer from \(z\). Indeed, if all components had remotes, each component could have at most \(k-2\) remotes outside it, which would force order at most \(3k+1\).

The component \(K\) has at least \(k-3\) vertices, and the entire second layer has at most \(k\). Every other component has at least two ports in that layer by 2-connectivity, so there is exactly one other component. There are two or three ports in it. The [three-port analysis](degree-four-three-ports.md) excludes three ports for all \(k\ge5\). With two ports, the [two-port construction](degree-four-two-ports.md) supplies a spanning path using a marked path of the large component and a route through the four anchors, the root, and \(K\).

The conclusion holds with no upper order restriction. It applies to the unique-low degree-four regime and leaves the connected-complement case open.
