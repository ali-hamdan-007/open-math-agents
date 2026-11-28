# The two remaining degree-24 populations

The preceding population argument leaves (x,y)=(22,83) and (33,72) at k=24 and n≥109. The following refinement is a paper proof with a reproducible finite computation. Its comparison with the exact parent is inherited from the three-cut saturation note.

## Common label residual

If a small-side label i is common and no high small-side vertex has all three labels, let the two other labels be D. Use the notation from Graph189PrivateQuota.residual_singleton_quota. PD counts high B-ports that miss i; HN counts high B-nonports at distance two from i; PC denotes the remaining high ports and GN the remaining high nonports. Its row estimates give

    PD + 2(PC+GN) ≤ 2k+x+2,
    PD ≤ 2k−2,     HN ≤ k,       y=PD+PC+GN+HN.

If PD is positive then HN≤k−1. Otherwise all positive even slots at i would already be occupied by HN. Each of the two residual labels j has a high representative in A adjacent to j and i. Thus j must be adjacent to i, since distance two from i is reserved for HN. But a PD vertex touches some such j and misses i, placing it at distance two from i as well. This is impossible. If PD=0, its own bound has slack at least two for k≥2. In either case

    2y ≤ 6k+x−2.

This eliminates (22,83), which had equality in the previous 2y≤6k+x bound. It also eliminates the last high-y population at k=23.

## The other population

The finite checker enumerates all three columns of the cut, up to simultaneous permutations. Its inputs are x,y,k and the two cross-column capacity bounds from the previous note. Here those are 22 and 23. It includes a column triple only if it could attain the required cross-product even when every second-layer slot is used by its larger first-layer coefficient.

For fixed column sizes a_i,b_i, the presence of pairwise intersections among the three source columns defines a graph on three labels. The program tests all eight graphs on each side. Each present edge ij implies |B_i∪B_j|≤k as seen by the opposite representative; an absent edge forces a_i+a_j≤x. When the intersection graph has at most two edges, it is a star or empty. In a star, intersections with different leaves are disjoint, so their total size is at most the center size. A leaf whose opposite column has size k−1 or k must place all its contacts in its incident intersection, by the minimum-cut debit; the same rule for the center fixes the total intersection size to the center size. The triangle case permits all cardinalities up to the population size, a relaxation. These rules give sound upper bounds for the number of ports.

Both the port union and the opposite intersection graph supply further bounds recorded in the script. In particular a column of size ≥k−1 forces another label to have a common opposite contact with it: the minimum separator supplies some opposite contact, and the debit forces at least two labels on that contact. If all three columns are near full, their correlation graph has no isolated label and has two edges sharing a center.

At a column with b_i≥k−1, the boundary argument from the near-saturation lemma gives at least x−a_i−(k−b_i) high A-vertices at distance two from i. If A_i and A_j share a contact, apply the same closed-neighborhood bound at that contact to obtain x−a_j−(k−b_i) at distance two from j. The symmetric estimates hold on B. At each label the two second-layer counts sum to at most k. Every high nonport of B must occur in a B second-layer column when x>k, and symmetrically for A. If either side contains a high nonport, the other side has at most k−3 high nonports by its mandatory debit.

For each allowable case the program maximizes the exact odd cross-pair cost

    Σ(a_i B2_i + b_i A2_i).

It fills each anchor's combined second layers to k to obtain an upper bound. At fixed total B2 the optimal assignment fills in decreasing order of a_i−b_i. It retains a case precisely when that upper bound and the contact sum would pay for all cross pairs in both orientations. At (33,72) none survives. Running three_cut_columns.py verifies both degree-24 exclusions in under a few seconds and leaves exactly (31,69) and (50,50) to that test at degree 23.

Together with the original kernel minimum-deletion lower order, this extends the paper range to k≥24. The all-order traceability theorem in Lean currently reaches k≥37, while the almost-full-column graph lemma has its own Lean certificate for arbitrary separator size.
