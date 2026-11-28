# Exterior order certificate for the final Graph 189 parameter intervals

Each row in verified-82.tsv is impossible for a nontraceable qualifying graph with the given connectivity s, second-smallest degree k and indicated inclusive order interval. The final column counts the remaining large-block tuples tested for that row. The argument uses only the upper endpoint of each interval. The file check.py is a standalone exact-integer verifier and has no dependency on the evolving research filters.

The intervals are the nonempty intersections of matching (s,k) rows of pointwise-input.tsv (the 280-row pointwise cut-separator projection) and column-input.tsv (the 87-row full active-column width projection). The original inputs are respectively ../../../global/arity/pointwise-survivors.tsv and ../../../lowblock/column-cancel-full.tsv. The proof here treats their 82 numerical intersections; the separate upstream results justify their coverage. The alternative width-only projection double-input.tsv has 64 intervals. Its separate verified-64.tsv output also excludes every row directly, without assuming interval containment.

| s | k range in the 82-row file | Actual orders across the rows | Row count | Large-block tuples |
|---|---:|---:|---:|---:|
| 5 | 53–81 | 342–538 | 29 | 61 |
| 6 | 82–109 | 615–831 | 28 | 86,830 |
| 7 | 117–141 | 998–1,214 | 25 | 791,190 |

The 82 individual lower and upper order bounds are listed in verified-82.tsv. The k ranges here are contiguous; the order endpoints apply separately to each row. The 64-row alternative covers 24, 22 and 18 pairs at s=5,6,7 respectively, with 702,730 remaining large-block tuples in total.

## Graph reduction used by the verifier

Let h=ceil(k/2), U the specified row upper, P a longest path maximizing the sum of squared exterior component sizes, and C a smallest high-bearing component of G−P. An exterior consisting only of the low singleton was previously excluded. Every high exterior member has at least h neighbors inside C. The reductions in ../../k10/uniform-matching.md and ../../../global/max-degree-plus-two-exception.md separate three cases.

For a 2-connected C of order m≤2q−1, with q its least high internal degree, let j be its largest contact matching. Connectivity gives j≥s. The unrestricted matched-exterior and near-size results give 3j<k, m≥k−floor(j/2)+2 and n≥(j+2)m+j−1. The necessary lower order exceeds U in every input row. The exact size bound allowing an arbitrary single low vertex is ../../../verify/near-hc-exterior-size.md. No subsequent sparse-root improvement is needed.

For a small endblock of order b≤2q−2, an endblock with all its noncut vertices high exists. The original endblock matching bound gives n≥3h−1+min((h+1)(k−h+2),(s+1)(k−s+2)). This exceeds U in each row, without any new tail gain or small-cut population test.

For a remaining 2-connected whole C choose B=C with order at least 2q, or choose a large endblock B of order at least 2q−1. In an endblock q denotes minimum degree inside B among noncut members. These are high. The sole possible exceptional block vertex is its articulation, or the low vertex if B=C. The remainder C−B in the endblock case contains at least h vertices. The cycle and s-connector estimate gives n≥(s+5)q+2s−1 in a whole, with a further h−3 in an endblock. Choose the corresponding good minimizing vertex x and put H=N_C[x], R the ambient second layer of x inside C, r=|R|. We have |H|=q+1, all H neighbors in C lie in H∪R and r≤2q−k+1; the final one is possible only with the low on P. The optimized local contact proof also gives degree at least k−q in H to every high H member. The small choice r≤1 would allow only q+2 vertices in the 2-connected B: its internal second layer from x lies inside R and cannot be a singleton separator. This contradicts the designated large order.

The verifier checks q−r−3>0 in every entire remaining range. Thus I, the vertices of B outside H∪R and the one possible exceptional vertex, is nonempty. Any member of I has q or more block neighbors outside H. Hence |B|≥2q+2. Set m₀=2q+2 in a whole, m₀=2q+2+h in an endblock: |C|≥m₀. In a whole the previous cycle lower improves by two because it had counted only 2q exterior vertices. The minimum degree in I is at least q−r−1, improved by one when no block exception remains outside H∪R.

Delete the low vertex from H if present and write H* for the result, l=|H|−|H*| and d=k−q−l. H* has size q+1−l, a universal vertex x and minimum degree at least d. Any prescribed pair spans a route of order d+1: with both endpoints different from x, take a longest path rooted at the first avoiding x and the second endpoint and then append x and that endpoint; with one endpoint x delete it first and append it last. If 2d≥|H*|+1, all |H*| are available by ordinary terminal-marker closure. The same length works when l=1, 2d=|H*| and d≥3. In full H every high vertex has degree at least d+1, half of |H|+1. If the low vertex has at least three H neighbors, H is Hamilton-connected by the one-exception terminal lemma. Otherwise one of its at most two H neighbors is x, so H* has at most one non-x degree below d+1 and even that degree is at least three. Thus H* is Hamilton-connected in this case. Write L for the certified route length. Using full H rather than H* allows trimming any tail connector from the last member of H before I.

Let J be the largest matching from H* to P. Each H* vertex needs at least k−q−r path contacts, while x needs k−q>0. A size-(k−q−r) cover when this quantity is positive would have to consist of real path marks only (H* has more vertices), insufficient for x. Thus J≥max(1,k−q−r+1). The J+1 path pieces consist of J−1 inner gaps and two tails. Each uses L vertices and each tail can also continue past H* to I in B with its terminal v deleted: connect H*−v to I, trim from the last H* member, and then continue from the first I vertex on a rooted I path. There is at least one intermediary since H and I are anticomplete. Each tail therefore gains at least q−r+1+c with c=1 when l=1 or when B=C and r=2q−k+1, and zero otherwise. In the first case the exception lies in H and in the second C is wholly high. Consequently the verifier only retains J when n≥m₀+J+(J+1)L+2(q−r+1+c) is at most U.

## The remaining finite inequalities

A minimum cover of the H*-to-P contact edges has p real marks and u=J−p covered H* members. The remaining w=|H*|−u high vertices W are nonempty in all tested rows. Every W vertex has degree at least k and all neighbors lie in H∪R and those p marks, so each misses at most a=q+r+p−k edges among those potential neighbors. The vertices available to enlarge H* are R and the low vertex in H if present, altogether r+l candidates. In nonincreasing order of W-neighbor count, the g-th best (numbering from one) has at least

    w − floor(wa/(r+l−g+1))

neighbors in W. Otherwise it and every later candidate would consume more than the wa missing W incidences. Retain only candidates with at least two guaranteed W neighbors, which places each inside B even if B is an endblock.

For each g from zero through r+l, set K to be H* and the g best choices, of order N=|H*|+g. All W vertices have degree at least N−1−a in K. When k−q>p the cover must contain x, of degree at least |H*|−1 in K. Each other covered H* member has degree at least d, and additions have the ordered degrees just proved. Either of two tests ensures K is Hamilton-connected:

- Its minimum degree is at least three and at most one vertex falls below ceil((N+1)/2). In the closure after adjoining the degree-two prescribed-endpoint marker, all high vertices become a clique; the sole low can be included because it has at least three neighbors, so one lies outside the prescribed pair.
- N≥2a+3, 2w≥N+1 and every K vertex outside W has degree at least a+2. In the same marker closure add W-to-W edges by the degree sum, then close W-to-other edges by (N−1−a)+(a+2)=N+1. All remaining vertices then have at least w neighbors each, and their missing pairs close.

The J direct H* contacts remain. Both tails can end a K traversal at a connector into I, gaining A=q−r+c more vertices beyond K. When g=0 the guaranteed intermediary gives one more. Therefore the candidate order is at least

    m₀+J+(J+1)N+2A.

Independently s disjoint connectors from K to P exist, as N≥s. Each interior connector vertex adds to the length of both bordering path pieces. If there are at least two connector-interior vertices, the gain is at least four. If there is one, at least one outer connector is direct and its tail can continue into I, giving at least 2+A. If all are direct both tails extend, gaining at least 2A. Hence the order is also at least

    m₀+s+(s+1)N+min(4,2+A,2A).

Every remaining large-block tuple has some g for which a certified K and at least one of these two lower bounds exceeds U. The fast code computes the two worst degrees among the selected ordered candidates when checking whether at most one degree is low. All inequalities have integer operands, and all range assertions are checked during replay. This certificate uses neither the newer path-bracket maximum on J nor a forced set of direct Menger links, an isolated-clique terminal classification, an H* connectivity assumption, or a new prescribed-path theorem.

## Reproduction and scope

Run python check.py to print verified-82.tsv, or python check.py --double for verified-64.tsv. The optional --s argument restricts a run to a single connectivity. The source checks the live-work lease before each row; this is operational and has no mathematical role. Cross-checking the numeric reduction uses the older audited geometry in ../five-through-25.md and the unconditional near-Hamilton-connected size proof cited above. This is an exact finite exterior certificate conditional on those graph-theoretic results, not an end-to-end Lean proof of the original conjecture.
