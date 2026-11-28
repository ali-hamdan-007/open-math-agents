# Independent audit of connectivity removal

Audited source SHA-256:

```text
3ce5291cb01c6bb71b334391486b93ef3091f411e4362390a88e0b38b8428345
```

This supplement correctly removes the 2-connectivity hypothesis on `F` from
the audited all-triples routing theorem.

## Components and cut parts

With `D=k-h+r-s`, every component of a disconnected `L` has order at least
`D+1`; every component of `L-w` at a cut vertex has order at least `D`.
The order inequality

```text
ell-3D <= 3s-f-b-2r
```

rules out three components in the disconnected case: it gives
`ell<=3D-2` in the large-expenditure case and `ell<=3D+2` in every remaining
case.

For a cut vertex with three parts, choose a `w`-neighbor `x_i` in each and let
`a_i` count the `w`-neighbors in that part.  The other-part contacts plus one
visible anchor give

```text
2a <= 3(k-1).
```

Inside its part, the closed neighborhood of `x_i` has at least `D` vertices;
all but at most `a_i` are exact distance-two witnesses from `w`.  Together
with an anchor witness for `w`, this gives

```text
3D-a <= k-1.
```

Hence `6D<=5(k-1)` and `k<=6h+6s-5<=6h+31`, contradicting
`k>=7h+84`.  Thus there are exactly two parts.

## Hamilton-connectedness of each part

A part of order `m` has `m<=ell-D-1` and internal minimum degree at least
`D-1`.  When `ell<=3D-2`, an endpoint marker gives augmented order `m+1`,
and every missing original pair has degree sum at least
`2D-2>=m+1`.  Selective cycle closure on original pairs therefore gives a
spanning path between any prescribed distinct original endpoints; the marker
retains degree two throughout.

In the remaining case, there are at most
`p<=b+r<=3s+1-f<=6` nonexclusive vertices in a part.  The exclusive internal
degree and the order bound show that all exclusive pairs qualify at threshold
`m+1`; the case split in the manuscript is exactly the inequality

```text
f+b+2r >= s+2q+2.
```

After completing the exclusive clique, `p<=d-2` makes every missing
exclusive--nonexclusive pair qualify.  For a final nonexclusive pair, either
its original degree sum `2d` qualifies or `m>=2d>=2p+1`, in which case both
vertices' completed adjacency to all `m-p` exclusives qualifies.  The
closure therefore proves genuine Hamilton-connectedness with the prescribed
endpoints; no unrooted endpoint assumption is used.

## Two cycles and attachment choices

Every part has an internal edge and hence a Hamilton cycle by closing a
prescribed spanning path.  In the cut case, `w` has two neighbors in one of
the two parts (its degree is much larger than two); a Hamilton path between
them closes through `w`, while the other part supplies its own cycle.  These
are two disjoint original cycles covering `L`.

Each part has a nonempty set of visible anchors.  If distinct anchors could
not be chosen across the two parts, both anchor sets would be the same
singleton and all part vertices would lie in one visibility class of size at
most `k-2`, contradicting `|X|+|Y|>=2D>k`.  Choose corresponding exceptional
ports.  If the two choices initially give the same port `J`, then `J` contains
both chosen anchors.  Since `|S_J|<=k-2<|X|+|Y|`, another exceptional port
touches one side; use it there and `J` on the other, choosing at `J` an anchor
different from the new port's assigned anchor.  Thus the reserved ports and
anchors really are distinct.

## Insertions and final route

The three eligible-edge counts from the base proof remain valid on a union
of two oriented cycles: successors are injective on that union, and every
`L`-neighbor lies on exactly one cycle.  Reserving two ports leaves at most
`h+e-2` insertion candidates, while every candidate has at least `h+e-1`
eligible original edges.  Greedy distinct subdivision therefore yields two
disjoint expanded cycles.  The subsequent disjoint `W` pairs and block
compatibility argument only gain capacity relative to the one-reserved-port
proof.

Open the first expanded cycle at its reserved contact `x` and the second at
`y`.  For distinct assigned anchors `a,b` and the third anchor `c`, the route

```text
(first cycle ending x)-P-a-z-c-(W blocks)-b-Q-y-(second cycle)
```

uses only explicit original edges and covers every vertex exactly once.

**Audit conclusion.**  The part counts, Hamilton-connected thresholds,
two-cycle insertion accounting, distinct port/anchor selection, and final
endpoint assembly are all sound.  The theorem holds under the stated
`k>=7h+84` threshold without any connectivity hypothesis on `F`.
