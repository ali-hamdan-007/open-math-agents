# Independent audit: large common-middle neighborhoods

Audited source SHA-256:

```text
74e0298fe62ba160db83116afa68b08a536787df625a7f3b84fd1ba5cbc7486a
```

## The Hamilton cycle in `F`

With `D=k-h-3`, the pair-intersection calculation for an independent set of
size `D+1` is valid and gives an original common `F`-neighbor for every pair.
If `x` in that independent set had a triple neighbor, then the triple's
`h+e+1` common-middle neighbors, one visible anchor, and the `D` independent
peers would give more than `k` disjoint even-distance witnesses.  Thus such
an `x` has no triple neighbor and `|N_F[x]|>=k-2`.

For an exceptional support `J`, its nontriple support has size at most
`k-h-2` and its boundary at most `e-2+a_J`.  The common-neighbor witnesses
give `a_J<=h+2`, so the closed-neighborhood packing bound is

```text
|I intersect S_J| <= e+1.
```

The `e` supports cannot cover `|I|=k-h-2>e(e+1)`.  Hence
`alpha(F)<=D`.

The ordinary independent-triple degree-sum bounds are correct.  In the sole
exceptional profile `f=7,b=3`, failure forces equality throughout:

* `m=3(k-h)-10`;
* the offending vertices all have `F`-degree `D`, three supporting ports,
  and all `h` triples as neighbors;
* the three pair-visible vertices are precisely this independent triple and
  share the double port and its two constituent privates.

The third exclusive class has at most `k-h-2` vertices, leaving at least
`2(k-h)-11` in the other two classes.  A fixed offending vertex is adjacent
to at most `D` of these, so at least `k-h-8` are distance-two witnesses via
the two privates.  Adding `h+e+1` common middles through a triple, two anchors,
and the two independent pair peers gives `k+e-3>k`.  This excludes the
exception and establishes the Bauer--Morgana--Schmeichel--Veldman cycle
criterion whenever `F` is 2-connected.

## Disconnected and cut cases

Every disconnected component has order at least `D+1`; every component of
`F-w` has order at least `D`.  Since `m<=3D+2`, a disconnected `F` has exactly
two components.  Three cut parts would imply `m>=3D+1`, hence `f+b<=8` and
`b<=1`.  Every part then contains an exclusive vertex, whose `F`-degree is at
least `D+1`; after deletion of `w` this forces each part to have at least
`D+1` vertices, contradicting `m<=3D+2`.  Thus a cut also yields exactly two
parts.

The endpoint-marker closure proving each part Hamilton-connected is sound.
In the large-expenditure branch, original internal degree sums already reach
the augmented order.  In the small branch, there are at most three
nonexclusive vertices.  The inequality

```text
f+b >= s+2q+2
```

completes the exclusive clique; the remaining cross pairs qualify because
the nonexclusive minimum degree is at least 19.  Final nonexclusive pairs
qualify either by their original sum or, after the cross completion, because
`m_0>=2p+1`.  The marker remains degree two, so prescribed endpoints are
preserved explicitly.

Consequently two disjoint original cycles cover `F`; in the cut case one
uses two neighbors of the cut vertex in a single part and closes its
Hamilton path through the cut vertex.

## Port insertions and the common-middle path

The distinct port/anchor selection for two cycles is valid because both an
exceptional nontriple support and an anchor-visible nontriple class have size
at most `k-h-2`, while the combined part size is at least `2D`.  If the first
two choices use one common port, another touching port exists and the
two-anchor mask of the common port supplies a distinct anchor.

For an unreserved port with `a_J<=e`, the successor-boundary count gives at
least

```text
k-2a_J-2e-h+1 >= (k-h)-4e+1 >= e-1
```

eligible original cycle edges.  This suffices for greedy insertion of every
such port.  Every remaining port has at least `e+1` common-middle neighbors.

For the induced graph on `W`, all triples, and the remaining high ports, add
an endpoint marker at prescribed distinct `W` vertices.  Its order is at
most `k+h`.  Original `W` degrees are at least `k-3-e`; the assumption
`k-h>=e(e+1)+3` implies `k-h>=2e+6`, so selective cycle closure first makes
`W` a clique.  The degree sums then add every triple--`W` edge and afterward
every high-port--`W` edge.  There are at most `h+p` satellites and
`|W|-1>=h+p`, so each satellite can occupy a distinct gap of a `W` spanning
path with the prescribed endpoints.  Closing through the untouched marker,
reversing closure, and deleting it yields an original endpoint-prescribed
path.

The final one-cycle and two-cycle concatenations use only explicit original
edges and cover every vertex exactly once.

**Audit conclusion.**  The `f=7,b=3` exception, component/cut analysis,
Hamilton-connected closures, port insertions, common-middle endpoint path,
and final assembly are all sound under
`k-h>=e(e+1)+3` and `|N_W(t)|>=h+e+1` for every triple.  No implicit endpoint
preservation is used.
