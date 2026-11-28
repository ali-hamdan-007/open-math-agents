# Independent audit of all-triples routing

Audited source SHA-256:

```text
1dd9b8da7fa9c1525c3512545e1ab2c8f846a6541c5befc68b48419d1ee2a891
```

## Selecting the cycle graph

For `L=F union Z`, every selected zero-`W` triple has at least
`k-e-(h-1)>=2` original neighbors in `F`; adjoining such vertices therefore
preserves 2-connectivity.  The order bound

```text
ell <= 3k-f-b-3h+r
```

is the exact anchor-visibility inequality after adding the `r` selected
triples.

In the large `b+f` case, `s=e`; in the small case the selection rule really
limits every selected triple to the three singleton masks, or four when one
private class is doubled.  Thus every `L` vertex has at most `s` exceptional
neighbors and

```text
delta(L)>=D=k-h+r-s.
```

The pair-common-neighbor calculation is sound.  In the large case
`3D>=ell+2` is more than enough for two degree-`D` neighborhoods in
`L-I` to intersect.  In the small case the strict inequality

```text
s_x+s_y < f+b+2r-s+1
```

follows from the stated doubled/non-doubled template bounds.  Hence all
independent peers used later are original distance-two witnesses.

For an exceptional support `S_J`, the common-neighbor property, the `W`
neighbors of `J`, and an anchor give

```text
a_J <= h-r+s-1.
```

The closed remote neighborhood has size at least `k-s+1` inside `H_J`, so

```text
|I intersect S_J| <= h-r+e+2s-5.
```

Summing over the `e` supports contradicts the displayed threshold.  The
uniform hypothesis implies it even in the worst case `e=s=6,r=1`:
the required right side is at most `7h+77`, below `7h+84`.  Therefore
`alpha(L)<=D`.

The independent-triple sum is also correct.  The large case already has
`3D>=ell+2`.  In the small case the required middle-neighbor bound is exactly
`f+b+2r-2`; the doubled estimate `6+b+2r` uses `f>=8`, and the non-doubled
estimate `min(9,3+2b+2r)` covers separately `b<=2` and `b>=3,r>=1`.
Together with `3D>=3 alpha(L)`, the cited Bauer--Morgana--Schmeichel--Veldman
criterion gives a Hamilton cycle in the original induced graph `L`.

## Inserting omitted triples and exceptional ports

Every unselected zero-`W` triple has a double-mask supporting port.  Its
support has size at most `b+h`, yielding

```text
a_J >= k-b-h-e-1.
```

The triple counts these common ports and all three anchors at distance two,
so it has at least `k-b-2h-2e+3` eligible original cycle edges.  This exceeds
`h+e-1` under `b<=12,e<=6,k>=7h+84`.

A remaining triple with `1<=a<2h` uses a neighboring `w in W`.  All but at
most `h+2` of its `W`-nonneighbors see `w`, producing the stated bound

```text
|D2(t) intersect L| <= e+a+h-1.
```

Its eligible-edge count is at least `k-6h-2e+4`, again at least `h+e-1`.

For a low-`a_J` exceptional port, the remote-boundary estimate gives at least
`k-5h-6e+7` eligible edges.  There are at most `h+e-1` total insertions in
these three classes, and every candidate has at least that many eligible
edges, so greedy selection of distinct original edges is valid.  Subdividing
adjacent chosen edges repeats no cycle vertex.  Even if a triple subdivides
an edge incident with `q`, deleting one expanded-cycle edge at `q` produces
a genuine spanning path beginning at `q`; no endpoint-preserving closure is
being invoked.

## `W` blocks and final route

All unassigned triples have at least `2h` `W` neighbors, so their disjoint
pairs can be selected greedily.  Every remaining unreserved exceptional port
has at least `2(h+e-1)` choices; before its last selection at most
`2h+2(e-2)` are occupied.  Thus all pair blocks are disjoint and

```text
B_0 >= k-h-2e+1 >= 4h+10.
```

Block compatibility requires both joining directions for the fixed block
orientations.  Distinct first and last `W` endpoints show that a block has at
most `2(h+2)` incompatible partners.  Dirac therefore gives a block Hamilton
cycle, and opening it yields an original-edge path ending in `W`.

The final concatenation is explicit: the terminal `W` enters the four-vertex
anchor--`z` path, which ends at the chosen anchor `i`, followed by
`i-P-q` and the expanded `L` path starting at `q`.  The reserved private is
the sole middle neighbor of `q`, so all vertices are covered exactly once.

**Audit conclusion.**  The large/small selection split, independence and
degree-sum bounds after adjoining zero-`W` triples, every insertion count,
the block route, and the sufficient threshold `k>=7h+84` are sound.  The
proof contains no implicit endpoint-preservation step.
