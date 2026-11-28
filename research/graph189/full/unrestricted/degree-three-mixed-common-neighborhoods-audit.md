# Independent audit: mixed common-middle degrees

Audited SHA-256: `0c2e5e2bd0e0ffe7ba4eb93dea9386c196af3abc084ee33042ceaa6fff0104fb`.

With `g=|B_H|`, `r=h-g`, `K=k-g`, removing the high triples correctly changes
the visibility allowance to `K-f_i` and gives
`|R'|<=3K-f-b-2r`.  The selected graph satisfies
`delta(L)>=D=K-r+u-s` and the stated order bound.

The independent-pair and support-packing arguments are the audited
all-triples proof with effective parameters `K,r`.  A member of the large
independent set cannot neighbor `B_H`, since the `h+e+1` common middles, one
anchor and its `D` peers already exceed `k`.  This yields
`|I intersect S'_J|<=r-u+e+2s-5` and contradicts the threshold implied by
`K-g>=7r+84`.  In the sole `f=7,b=3,u=0` profile, equality forces adjacency
to all `h` triples; because `g>=1`, a high triple supplies the required
`h+e+1` W-witnesses and the exceptional profile is impossible.  Thus the
independent-triple Hamilton-cycle criterion is valid.

The disconnected/cut analysis leaves exactly two Hamilton-connected parts.
The hard closure has at most six nonexclusive vertices; all exclusive,
cross, and final-pair degree sums reach the endpoint-marker threshold.
Nontriple population bounds give distinct reserved ports and anchors.

The three insertion classes have respectively at least

```text
K-g-b-2r-2e+3,
K-g-6r-2e+4,
K-5r-6e+7
```

eligible original cycle edges, each at least `r+e-1`.  Greedy subdivisions
and subsequent disjoint W-pair assignments are therefore sound.

In the outer graph, W-degree sums reach its order because
`K>=3r+2e+6`.  After W becomes a clique, every `B_H` vertex qualifies against
all W.  The block count leaves at least `g` gaps by `K>=r+2e`, so the high
triples can be placed individually.  The untouched endpoint marker makes
closure reversal rooted, and the final one-/two-cycle routes are explicit.

**Conclusion.**  The theorem is sound under `k>=2g+7r+84`; effective-K
substitution, the exceptional profile, connectivity removal, insertions,
outer closure and endpoint assembly all pass.
