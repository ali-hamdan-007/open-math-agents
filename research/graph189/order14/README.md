# Graph 189 at order fourteen

Consider a finite connected simple graph of diameter at most three, order fourteen and minimum degree two. Count each vertex itself among its even-distance vertices. Suppose the second-smallest degree is five and each vertex has at most six even-distance vertices. Under these hypotheses the graph has a Hamiltonian path. The following proof concerns this degree-two subcase of the DeLaViña conjecture.

## How the lemmas fit together

Choose a vertex of degree two and call its neighbors the anchors. All other vertices have degree at least five. Each vertex has at most five vertices at distance exactly two.

1. The [layout lemma](../../Graph189Order14Layout.lean) leaves five possibilities for the adjacencies between the anchors and their distance-two layer. The [relabeling lemma](../../Graph189Order14Relabel.lean) gives consecutive labels to the corresponding vertex sets. Both files have been checked by the Lean kernel.
2. Four handwritten arguments rule out four layouts by counting distinct vertices at distance two. They handle the [four-vertex middle layer](adjacent-four-middle.md), [nonadjacent anchors](nonadjacent.md), [two misses each](adjacent-two-two.md), and [one and two misses](adjacent-one-two.md).
3. In the [remaining layout](path.md), each anchor misses a different middle vertex. The six remote vertices contain a Hamiltonian cycle. The other eight vertices have a spanning path ending at a middle vertex attached to a remote vertex. Break the remote cycle at that neighbor and use the attachment edge to concatenate the two paths.

The path assembly uses the same operation already formalized as `IndexedPath.flatten_block_chain` in [reduction #5336](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5336). For disjoint blocks a spanning path in each block and an edge between their endpoints suffice. The direct argument gives a handwritten proof of the order-fourteen conclusion. End-to-end Lean verification and an official upstream verdict are separate milestones.

The [independent outer-layer argument](outer-layer.md) also gives a general bound on the size of the layer at distance three. The available OMA child allows other values of the second-smallest degree.
