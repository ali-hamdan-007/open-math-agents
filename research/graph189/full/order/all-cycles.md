# Sharp order for clique blow-ups of arbitrary cycles

Let a simple cycle of length ℓ≥3 have its vertices replaced by arbitrary nonempty cliques, with complete links between consecutive cliques. Assume that at most k other vertices lie at positive even distance from each vertex, where k is the second-smallest degree. Then the largest possible order over *all* cycle lengths equals

* ⌊(10k+1)/3⌋ for k=2 and every k≥4;
* 8 for k=3.

The graph has diameter at most two if ℓ≤5. For a vertex of minimum degree, every other vertex is either adjacent or at distance two, giving n≤2k+1.

For even length ℓ=2h≥6, two different index classes have even distance exactly when their indices have the same parity. Within the same clique distances between other vertices are one. Write W for the total clique size on one parity. Each of the h constraints there reads W−sᵢ≤k. Summing gives (h−1)W≤hk. Hence n≤2⌊hk/(h−1)⌋≤3k.

For odd length ℓ=2h+1≥9, every class sees exactly 2⌊h/2⌋ whole other classes at positive even distance. Each class occurs in that many inequalities by cyclic symmetry. Thus n≤(2h+1)k/(2⌊h/2⌋)≤11k/4, since h≥4.

Only ℓ=7 can exceed 3k. The companion proof sharp-seven-cycle.md gives that case's exact maximum ⌊(10k+1)/3⌋ for k=2 and k≥4, and excludes k=3. At k=3, for ℓ≤5 the order is at most seven; for odd ℓ≥9 it is at most eight. At even ℓ≥6, each parity has W≤⌊3h/(h−1)⌋≤4, so n≤8. To attain eight, take a six-cycle, give each of two opposite classes size two, and give every other class size one. All degrees are three. Each parity weighs four, so all positive even-distance counts are at most three. Every constructed graph has a Hamiltonian cycle.
