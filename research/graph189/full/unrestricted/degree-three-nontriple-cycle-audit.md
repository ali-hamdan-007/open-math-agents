# Independent audit of `degree-three-nontriple-cycle.md`

Audited source SHA-256:

```text
a15b701cda29ff2edb3dcc1c25bfb38eb2f6945ede986181f292883a4030a2f4
```

## Remote-cycle criterion

The visibility count is exact:

```text
m+b+3h = sum_i |V_i| <= 3k-f.
```

A nontriple remote sees no common port and has at most three exceptional
port neighbors, so `delta(F)>=D=k-h-3`.  In the two `f=7` templates an
exclusive remote has one port neighbor; in all other cases the stated
two/three bounds are valid.

If an independent set `I` had size `D+1`, the inequalities in the manuscript
make every pair in `I` share an `F`-neighbor.  The strict inequality is in
the correct direction:

```text
d_F(x)+d_F(y) > |F-I|.
```

Thus all other members of `I` are exact distance-two witnesses from a fixed
member.  For an exceptional port `J`, its support and remote boundary satisfy

```text
|S_J|<=k-2,       |H_J-S_J|<=e-2+a_J.
```

The latter correctly counts missed common ports, `z`, and a missed anchor.
The anchor exists because every exceptional mask is proper and the anchor
graph is connected.  The closed-neighborhood argument then gives

```text
|I intersect S_J| <= e-1+a_J <= h+e+1.
```

Summing over the `e` exceptional supports contradicts
`k >= (e+1)h+e(e+1)+3`.  Hence `alpha(F)<=D`.

For an independent triple, its degree sum is at least
`3k-3h-s`; the visibility equation shows that `s<=f+b-2` is exactly what is
needed for the `m+2` bound.  The manuscript's template bounds cover every
case except `f=7,b=3`.  In that exception, a common port cannot see three
exceptional ports: if it misses `J`, the nontriples outside an anchor
visibility containing `J` already give at least `k+1` even witnesses.  It
also cannot see all four.  Therefore `sum_J a_J<=2(k-4)`, the four remote
boundaries have total size at most `2k`, and every exclusive remote belongs
to one of them.  Hence `m<=2k+3`, and the specialized threshold
`k>=5h+23` gives `3D>=m+2`.

Thus every independent triple has degree sum at least both `m+2` and
`3 alpha(F)`.  The cited Bauer--Morgana--Schmeichel--Veldman circumference
bound then gives a Hamilton cycle because `F` is 2-connected.  This is an
actual cycle in the original induced graph; no closure or endpoint reversal
is hidden in this step.  If there is no independent triple, the usual
infinite-`sigma_3` convention (or Chvatal--Erdos with `alpha(F)<=2`) gives the
same conclusion.

## Expanding the remote cycle

At least two anchor classes have a unique true private.  For such a class
`i`, inclusion-exclusion yields at least `h+3` exclusive remotes.  Each has
the chosen private `P` as its sole port neighbor.  Choosing `q` among them
and reserving `P` ensures that no edge incident with `q` is later subdivided.

For an unreserved exceptional port `J` with
`a_J<M=2(h+e-1)`, the number of cycle edges with both endpoints adjacent to
`J` is at least

```text
k-2a_J-2e-h+1 >= k-5h-6e+7 >= e-1.
```

There are at most `e-1` such ports, so distinct edges can be selected
greedily.  Subdividing adjacent selected cycle edges is safe: their shared
cycle endpoint appears only once in the expanded cycle.  The reserved
private is the sole port neighbor of `q`, so the opened cycle really starts
at `q`.

## Doubled Hall assignment and block route

For two copies of every triple, adjoining one universal dummy right vertex
turns

```text
|N_W(S)| >= 2|S|-1
```

into Hall's condition for every subset of copies.  Removing the dummy leaves
at most one unmatched copy total, and the other copy of that triple is still
matched to an actual `W` vertex.  The stated per-triple condition
`|N_W(t)|>=2h-1` indeed implies the subset condition because every nonempty
`S` contains one such neighborhood and `|S|<=h`.

Every remaining high-`a_J` exceptional port can then take two fresh
`W` neighbors: before the last choice at most
`2h+2(e-2)=M-2` vertices are unavailable, while `a_J>=M`.

After forming the full-pair blocks, singleton blocks, and possibly the
partially matched singleton `w_0`, the block count satisfies

```text
B_0 >= k-h-2e+1.
```

Compatibility between blocks requires both directed joining edges: the last
endpoint of either block sees the first endpoint of the other.  A fixed block
can fail this for at most `2(h+2)` other blocks, because first endpoints are
distinct and last endpoints are distinct.  The main threshold gives
`B_0>=4h+10`, so Dirac supplies a Hamilton cycle of the compatibility graph.
Opening it at `w_0` when needed and traversing all blocks in their fixed
orientations uses only original graph edges.  Prepending the unmatched triple
uses its retained matched edge to `w_0`.

## Final endpoint assembly and threshold

The block path ends in `W`, hence can enter any anchor.  The four-vertex
anchor--`z` shell has the explicitly described spanning path ending at the
chosen anchor `i`.  The final concatenation

```text
(triple/W blocks) -- W -- (anchor shell ending i) -- P -- q
    -- (opened expanded F-cycle)
```

covers every vertex exactly once.  In particular, `q` is not repeated and no
ordinary closure theorem is being asked to preserve an endpoint.

All auxiliary inequalities follow from

```text
k >= (e+1)h + e(e+1) + 3,
```

and the uniform `k>=7h+45` is exactly the maximum over `e=4,5,6`.

**Audit conclusion.**  The Hamilton-cycle criterion, doubled subset-Hall
condition, exceptional-port insertions, block Dirac route, final endpoint
assembly, and stated thresholds are sound.  No implicit endpoint-preservation
step was found.
