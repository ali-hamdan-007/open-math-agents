# Independent audit of the final exterior exclusions

The independently written integer checker exterior-simpler/independent_core.py excludes every one of the 64 order envelopes in lowblock/independent-double-matched.tsv. That input is byte-for-byte identical to lowblock/independent-double-cross.tsv, obtained by a different lower-order test. The checker uses the upper endpoint of every interval for each contradiction. Its only package imports are from the Python standard library.

| Connectivity | Second-smallest degrees | Envelopes excluded |
|---|---|---:|
| 5 | 58 through 81 | 24 |
| 6 | 88 through 109 | 22 |
| 7 | 124 through 141 | 18 |

The same program excludes all 82 envelopes obtained by intersecting global/arity/pointwise-survivors.tsv with lowblock/column-cancel-full.tsv. These comprise 29, 28 and 25 at connectivities 5, 6 and 7 respectively. Both routes use the original large-block estimates in sep/cover/five-through-25.md. They do not require the later extras from a tight clique, strengthened Menger connector accounting, a special connectivity-seven rule or a three-connected neighborhood.

## Why the alternatives exhaust a nontraceable graph

Suppose G is nontraceable. Choose a longest path P maximizing the sum of squared exterior component orders, then choose a smallest exterior component C containing a high vertex. Such a component exists, since at most one vertex is low and the near-spanning gap theorem excludes a path missing just that vertex. Each high member of C has at least h=ceil(k/2) neighbors in C, and |C|≥h+2. If C has an articulation, the block-cut tree has at least two terminal blocks. Select one, B, all of whose noncuts are high. A terminal bridge cannot have a high noncut since h≥2. Also C outside B contains a high vertex. Otherwise it consists of the single low z adjacent internally only to the articulation v. The rechecked adjacent-exterior contact count gives k≥a_z+d(v)−1, since z and v share no exterior neighbor. Hence z has at most one path contact and total degree at most two, contradicting connectivity at least five. Taking a high vertex outside B and its internal neighbors gives |C outside B|≥h, since only its articulation can be a neighbor in B. Thus the whole-component and terminal-block lower bounds both hold without an assumption on the location of the low.

If C is 2-connected with order ≤2q−1 (q the least internal degree among high vertices), the independent near-Hamilton-connected size lemma gives 3j<k and m≥max(h+2,k−floor(j/2)+2). Minimum-cut matching gives j≥s. At most one pair of distinct prescribed terminals can fail to have a spanning route, so n≥(j+2)m+j−1. The program directly tries all such j. For a terminal block of order b≤2q−2, it checks (j+2)b+3h−1 at j=max(s−1,k−b+1) for every feasible b. These inequalities alone eliminate every small and near alternative in both datasets.

The remaining cases are a whole 2-connected C of order ≥2q or a terminal block of order ≥2q−1. Fan's cycle and s disjoint connectors give the initial q range in sep/k10/uniform-matching.md. For x of minimum good degree, H=N_C[x] and R the members of C at ambient distance two from x, write r=|R|. Block connectivity rules out r≤1 since deleting at most one second-layer member could not separate H from further points, yet the preliminary block has ≥2q−1 vertices. The optimized path exchange gives r≤2q−k+1, with the upper endpoint allowed only when the low is on P. Every numerically considered regime has q<k and q−r−3>0, asserted during enumeration. There is consequently a high, nonexceptional block vertex beyond H,R whose q neighbors all miss H; this gives block order ≥2q+2. The case distinction thus includes all values of r and of the low indicator in H.

For each remaining j and contact cover with u covered H vertices the program ranges over every integer u from zero through j. It checks that a covered H vertex exists when x's contact demand exceeds the number of real marks, and that the uncovered vertices' missing-edge allowance is nonnegative. Its assertion j<|H*| actually holds on every row where this issue is reached, with H* the high part of H. The degree tests for the enlarged Hamilton-connected set, including the possible single degree-three exception and the case 2δ(H*)=|H*| with a low H member, are exactly the original endpoint-closure tests in five-through-25.md. The direct-contact and disjoint-connector bounds are computed independently. On a tail through matched v, B−v remains connected. The connector continuing toward I is chosen from the last retained core vertex, so it never reuses the core traversal. Two distinct interior connector vertices improve neighboring piece bounds separately by four. With one interior connector vertex at least one outer connector is direct and supplies its tail extension. The program uses the weaker minimum of these direct and indirect improvements. It makes no assumption of simultaneously using all these alternative tails in one path.

## Reproduction and scope

From the packet root run the following.

```sh
python verify/exterior-simpler/independent_core.py lowblock/independent-double-matched.tsv lowblock/independent-double-matched.tsv
python verify/exterior-simpler/independent_core.py global/arity/pointwise-survivors.tsv lowblock/column-cancel-full.tsv
```

The first run produces 64 exclusions, the second 82. Recorded output is in verify/exterior-simpler/independent64.log and independent-final.log. The SHA-256 of the independent program is 46f46a1508a54839b0ed4578dcf346dbaa23266aa453b3bf0a5a6122e17723ef. The 64-row input has SHA-256 dcf24f7a3072bca5ffab575eb89fcfcc756ddf8a00576315bce7b6df5e883f52.

These are exhaustive numerical checks of necessary graph inequalities under the cited paper lemmas. They do not enumerate labelled graphs. The separate full-rectangle programs establish completeness of the input envelopes. This note verifies the exterior exclusions for every supplied envelope and records the mathematical preconditions. The local geodesic degree-width result has a separate Lean proof; this audit is not a kernel proof of final traceability.
