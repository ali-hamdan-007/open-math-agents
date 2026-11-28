# Traceability with one vertex above the second-smallest degree

Let $G$ be a finite connected simple graph with second-smallest degree $k$. Suppose every vertex has at most $k$ other vertices at even distance and at most one vertex has degree above $k$. Then $G$ has a Hamiltonian path.

If no vertex has degree above $k$, the [rooted local Ore theorem](../root/rooted-local-ore.md) gives the result at order above $3k+1$, and the established small-order theorem covers the remaining orders. Suppose instead that $h$ is the unique vertex of degree above $k$. There is at most one vertex of degree below $k$ by the choice of $k$.

The established cut-vertex theorem covers the graphs that are not 2-connected. At order at least $4k+1$, the [hub-deletion proof](unique-hub-deletion.md) gives traceability. At order at most $4k$, the [moderate-order theorem](moderate-order-all-degrees.md) covers connectivity at least three. The remaining connectivity-two case is covered by the [unique-hub separating-pair proof](unique-hub-separating-pair.md). The prior small-degree cases used in these proofs apply without an additional degree assumption.
