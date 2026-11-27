# Traceability up to the minimum degree plus twice the second-smallest degree

Let G be a finite connected simple graph of order n≥2, minimum degree δ and second-smallest degree σ. If every vertex has at most σ vertices at distance exactly two, then G is traceable whenever n≤δ+2σ. This applies to the full even-distance hypothesis without a diameter restriction.

Write α for the independence number. If an independent set I has at least σ+2 vertices, pick x∈I. Some y∈I, y≠x, is at distance at least three from x, since neither adjacency nor distance two can account for all the other members of I. Consequently N(x), N(y), I are pairwise disjoint. As any pair of distinct vertices has degree sum at least δ+σ, this gives n≥|I|+δ+σ≥δ+2σ+2. In particular, n≤δ+2σ+1 implies α≤σ+1.

Add a universal vertex to obtain H, which is 2-connected: deleting the universal vertex leaves connected G, and deleting any original vertex leaves the universal vertex. Set c=κ(H)≥2. The independence number of H equals α(G). If α≤c, the Chvátal–Erdős theorem yields a Hamilton cycle in H. Equivalently, the degree-sum criterion below takes its independent-set sum to be infinity if no set of the desired size exists.

Otherwise every independent set of size c+1 in H lies wholly in G. At most one original vertex is below degree σ in G, so such a set has degree sum at least δ+cσ+c+1 in H. Chiba, Furuya, Ozeki, Tsugaki and Yamashita proved that a c-connected graph H is Hamiltonian if its minimum degree sum over independent (c+1)-sets is at least |H|+κ(H)+(c−2)(α(H)−1). In the present case the latter quantity is at most n+1+c+(c−2)σ, which is at most δ+cσ+c+1, exactly because n≤δ+2σ. Hence H has a Hamilton cycle; deleting the universal vertex yields a spanning path in G.

This gives order 3σ when δ=σ. It improves the 2σ+3 cutoff of Easwar–Johari when δ≥4; when δ≤3 their result is at least as strong.

**Sources.** S. Chiba, M. Furuya, K. Ozeki, M. Tsugaki and T. Yamashita, “A Degree Sum Condition on the Order, the Connectivity and the Independence Number for Hamiltonicity,” Electronic Journal of Combinatorics 26(4), P4.53 (2019), Theorem 2. [Published article](https://doi.org/10.37236/5480) · [Preprint](https://arxiv.org/abs/1804.01258). R. Easwar and S. Johari, “Conditions for traceability under a bound on the size of even-distance sets,” Theorem B. [Preprint](https://arxiv.org/abs/2609.11719).
