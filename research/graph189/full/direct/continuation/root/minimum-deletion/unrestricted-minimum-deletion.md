# Hamiltonian minimum deletion for every degree at least three

Assume the exact Graph 189 even-distance bound in a finite connected graph G. Write k for its second-smallest degree and choose a vertex z of minimum degree δ. If k≥5, δ≥3 and G−z has a Hamiltonian path, then G has a Hamiltonian path. No connectivity or order restriction is needed beyond connectedness. The following paper proof uses locally checked graph-facing rooted lemmas. The new path census and gluing have not been kernel-checked as a joint theorem.

Assume a counterexample. Among paths containing z choose a longest path P; write m for the number of omitted vertices, u=k+1−m and n=|G|. The checked rooted-exterior, matching-order and strict-matching results give 2δ≤k, δ+1≤u≤m and m+u=k+1. They also give Hamilton-connectedness of the subgraph on the exterior E. Every exterior vertex has original degree at least k, at most m−1 neighbors in E, and hence at least u distinct neighbors on P. Every one of these facts holds for every equally long path containing z.

The fork's prior lowblock/all-near-spanning.md already proved the almost-spanning implication on paper and introduced the private/shared contact groups used below. Its exchange uses one tight gap and the path shifts at all marks. This version uses the independently checked strict matching allowance to obtain two tight gaps, allowing a direct cardinal contradiction after two exchanges. It supplies a modular formalization route for the earlier paper result.

## All exterior vertices have the same u contacts

A mark is a position on P with at least one neighbor in E. Let M count marks. In their path order group consecutive marks whose set of exterior neighbors is the same singleton. Make each mark with multiple exterior neighbors its own one-mark group. Distinct successive groups therefore have distinct exterior representatives at their bordering marks. Let g be the number of groups.

Between successive groups, the entire exterior can replace the intervening unmarked interval via the two distinct representatives, by Hamilton-connectedness. Each exterior tail can also be attached at its bounding mark. Every one of these g+1 intervals and tails not containing z consequently has at least m vertices. If exactly one contains z, it has at least one vertex. If none contains z, the stronger full bound applies. This reasoning allows z to be a mark or to lie in an omitted intragroup interval. Counting the marks, exterior, and intergroup intervals gives

$$n\ge m+M+gm+1\ge(g+1)(m+1).$$

If every exterior vertex owns at least one singleton group then g≥m≥u. Otherwise some vertex has no singleton group and all of its at least u marks are shared marks, each forming its own group. Thus g≥u. Set σ=n−(u+1)(m+1)≥0.

Since δ+1≤u≤m and m+u=k+1, one has (u+1)(m+1)≥(δ+2)(k−δ+1). For example, the difference equals (u−δ−1)(m−δ−1), since u+m=k+1. The checked small-degree order ceiling gives n≤1+δ+k+δ(k+1−δ). Consequently σ≤3δ−k−1≤δ−1≤u−2. This makes g≥u+1 impossible, so g=u.

If every exterior vertex owned a singleton group, m≤g=u≤m would force m=g=u. Every one of these u groups would then belong to a different vertex, with no shared group left. Since every row has at least u marks, M≥u². The first counting inequality would give σ≥M−u≥u²−u>u−2. An exterior vertex lacking a singleton group therefore exists. All u groups must be its shared marks. The full mark set now has exactly u elements, and every exterior vertex has at least u neighbors there. Hence every exterior vertex is adjacent to the same set A of u marks. The identical reasoning applies to every equally long path through z.

## Two tight gaps give too many even distances

There are u+1 intervals and tails at these u marks. At least u avoid z. Each of those contains at least m vertices by the preceding detours. If all u+1 avoid z, then z is a mark and n≥m+u+(u+1)m, giving σ≥m−1>u−2. Thus z lies in an unmarked interval or tail, which contributes at least one vertex. Among the remaining u intervals and tails, at most σ can exceed m by at least one. At least u−σ≥2 are therefore disjoint intervals J₁,J₂ of exactly m vertices.

Independently replace each Jᵢ in P by a spanning path of E, using its one or two old bounding marks as appropriate. These attachments exist because all of E sees all of A and m≥2. Each replacement retains z and has the same order as P. Its exterior is exactly Jᵢ. On this new path the already proved uniformity says every vertex of Jᵢ has the same mark set. At least one old bounding mark lies on the new path and is adjacent to a vertex of Jᵢ by an original path edge. Thus every vertex of Jᵢ neighbors that bounding mark. In the original graph, each vertex of E is adjacent to the bounding mark and is adjacent to none of Jᵢ (those unmarked vertices had no exterior neighbors). Hence its distance to every member of J₁∪J₂ is exactly two.

The two original gaps are disjoint, each of size m. Any exterior vertex has at least 2m≥m+u=k+1 other vertices at distance two, contrary to the original allowance k. This proves traceability under the stated hypotheses.

## Existing interfaces and remaining formal work

The three graph-facing inputs are Graph189RootedSplice.near_spanning_rooted_exterior, rooted_matching_cone_order, and strict_matching_allowance. The order ceiling is Graph189LayerCutoff.order_of_small_degree. The existing common_marks_of_large_exterior already supplies uniformity whenever u<m. The mark-group argument adds the equality case u=m, while the two full-exterior gap exchanges handle all u. The existing two_tight_contact_gaps and two_tight_gaps_force_cap establish a related exchange for a single omitted root on a near-spanning path. Here the starting path is protected and omits m vertices, so the corresponding exchange needs its own checked transfer. This does not by itself address nontraceable minimum deletions in the full parent.


## Formalization checkpoint

The actual graph-facing declaration is Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion_unrestricted in Graph189UnrestrictedMinimumDeletion.lean. All of the following new modules are source drafts awaiting a pinned replay. Graph189UniformExchangeInterface reduces the graph-facing claim to its path-family exclusion. Graph189ContactGroupCensus, Graph189ProtectedGapCount and Graph189ContactIntervals derive the uniform row census from finite incidences and legal interval lengths. Graph189BalancedContactRows applies them to the path's actual contactPositions using the existing Graph189ProtectedIntervals and Graph189NearFinal. Graph189TwoProtectedGaps selects two full legal intervals. Graph189FullExteriorExchange constructs the path splices and distance-two witnesses. Graph189FullGapPositions returns the certified TightGap records and checks the protected root stays on the path. Graph189UnrestrictedMinimumDeletion joins these arguments. The small pure module Graph189ContactGroupCensus imports only Mathlib and can be checked first. The pinned Graph189ProtectedIntervals source is the existing lowblock/Graph189ProtectedIntervals.lean, using the shared Graph189ExteriorGap.olean.
