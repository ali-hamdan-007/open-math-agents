# Degree-five root: completion of the `(a,s)=(4,2)` extremes

Retain the notation and hypotheses of `degree-five-disconnected.md`.  Thus
`z` is the unique vertex of degree five, every other vertex has degree at
least `k>=7`, `K` is the component of `G-N[z]` contained in the second
layer, and `D` is the other component.  In the parameter case `(a,s)=(4,2)`
we have

    |K|=k-4,

and the two ports of `D` are denoted by `u,v`.  Write `R` for the third
layer in `D` and `F` for the fourth layer.  We prove that every remaining
extreme `|D|>2k` has a spanning marked path and hence that `G` is traceable.

Every vertex of `K` has no possible neighbours except the other `k-5`
vertices of `K` and the five anchors.  Its degree is at least `k`, so `K`
is a clique complete to every anchor.  Consequently `z` and all `k-4`
vertices of `K` are `k-3` distinct distance-two witnesses from either
port.  The argument in `degree-five-disconnected.md` also gives disjoint,
nonempty anchor-neighbourhoods for `u` and `v` and

    |N_R(u)| <= k-1,   |N_R(v)| <= k-1.

Let `b` be a marker adjacent only to `u,v`.

## One fourth-layer vertex

Suppose first that `|D|=2k+1` and `F={f}`.  Necessarily

    U=N_R(u),  V=N_R(v)

are disjoint and both have order `k-1`.  The vertex `f` has a neighbour in
each side: without (say) a `U`-neighbour, it would have at most `k-1`
possible neighbours in `V`, below its required degree `k`.

Let `E_V` be the vertices of `V` incident with a `U-V` edge.  At `u`, the
vertices `z`, `K`, `f`, and `E_V` are distinct vertices at distance exactly
two.  The even-distance cap therefore gives

    (k-3)+1+|E_V| <= k,

so `|E_V|<=2`.  A vertex of `U` can have neighbours outside `U` only among
`u`, `f`, and `E_V`; hence `delta(G[U])>=k-4`.  Symmetrically
`delta(G[V])>=k-4`.  Since both sides have order `k-1` and `k>=7`, Dirac's
theorem gives a Hamilton cycle in each side.

Choose `x in N(f) intersect U` and `y in N(f) intersect V`.  Delete a cycle
edge incident with `x` in the `U`-cycle and one incident with `y` in the
`V`-cycle.  Orient the resulting paths so that they end at `x` and begin at
`y`.  Their other endpoints are adjacent to their respective ports, and

    b,u, (all of U), x,f,y, (all of V), v

is a spanning path of `D+b` (with the displayed side-path orientations
understood).

## Two fourth-layer vertices

Now let `F={f,g}` and `|D|` be either `2k+1` or `2k+2`.  Put

    U=N_R(u),  V=N_R(v).

When `|D|=2k+2`, `|R|=2k-2`, so the port-neighbourhood bounds force `U,V`
to be disjoint and both of order `k-1`.  When `|D|=2k+1`, `|R|=2k-3`.
Then either `U,V` are disjoint with orders `k-1,k-2`, or they meet in one
vertex `w` and both have order `k-1`.  Indeed

    |U|+|V|=|R|+|U intersect V| <= 2k-2.

In the one-point-intersection case assign `w` to one side.  Thus in all
cases there is a disjoint partition

    R = X disjoint_union Y,   X subset U,   Y subset V,

where each side has order `k-2` or `k-1` (and both have order `k-1` when
`|D|=2k+2`).

There is no edge `uv`.  Otherwise every vertex of `V`, at least `k-2` of
them, would be at distance two from `u`, in addition to `z` and the `k-4`
vertices of `K`.  This exceeds the cap for `k>=6`.

Let `c=|U intersect V|`, so `c` is zero or one.  Define

* `F_X={h in F : N(h) intersect X is nonempty}`;
* `E_Y={y in Y : y has a neighbour in X}`.

Every member of `F_X` and `E_Y` is at distance exactly two from `u`.  If
`c=1`, the opposite port `v` is one further exact-distance-two witness via
`w` (recall that `uv` is absent).  Together with `z` and `K`, the cap at
`u` gives the exact cross-endpoint bound

    |F_X|+|E_Y|+c <= 3.                    (1)

For any `x in X`, all neighbours outside `X` lie among `u`, possibly `v`
when `x=w`, the vertices of `F_X`, and the vertices of `E_Y`.  Equation
(1) therefore gives

    d_D(x)-d_X(x) <= 1+c+|F_X|+|E_Y| <= 4.

Vertices of `R` have all their neighbours in `D`, so

    delta(G[X]) >= k-4.

The symmetric argument at `v` gives `delta(G[Y])>=k-4`, with one small
bookkeeping point when `U intersect V={w}` and `w` was assigned to `X`.
Write `F_Y` for the fourth-layer vertices meeting `Y` and `E_X` for the
vertices of `X` incident with an `X-Y` edge.  The vertex `w`, if it belongs
to `E_X`, is adjacent to `v` and hence is not itself a distance-two witness
from `v`; instead the opposite port `u` is a distance-two witness through
`w`.  Thus the cap gives

    |F_Y|+|E_X minus {w}|+1 <= 3.

Whether or not `w` belongs to `E_X`, this implies
`|F_Y|+|E_X|<=3`, so a vertex of `Y` still has at most four neighbours
outside `Y`.  As each side has order at most `k-1`, Dirac's theorem supplies
Hamilton cycles on both sides for every `k>=7`.

It remains only to place `f,g`.  Each has a neighbour in `X union Y`, since
its sole possible neighbour outside `R` is the other fourth-layer vertex.
Consider the incidence bipartite graph from `{f,g}` to the two symbols
`{X,Y}`, recording a nonempty neighbourhood in a side.

If it has a matching, label the matched vertices `f_X,f_Y` and choose
`x in N(f_X) intersect X`, `y in N(f_Y) intersect Y`.  Break the two
Hamilton cycles at `x,y`, orient their free endpoints toward `u,v`, and use

    f_X, x, (all of X), u, b, v, (all of Y), y, f_Y.

This is a spanning path of `D+b`.

If there is no matching, both fourth-layer vertices have neighbours only in
the same side, say `X`.  For either `h in {f,g}` the degree bound gives

    k <= d(h) <= |X|+1 <= k.

Thus `|X|=k-1`, `fg` is an edge, and both `f,g` are complete to `X`.
Breaking the two side cycles arbitrarily yields the spanning path

    f,g, (all of X), u, b, v, (all of Y).

## Expanding the marker

In all two-fourth-layer routes the marker is internal with path-neighbours
`u,v`.  Choose an anchor adjacent to `u` and an anchor adjacent to `v`;
they are distinct because the two anchor-neighbourhoods are disjoint.
The shell on `K`, the five anchors, and `z` has a spanning path between
these prescribed anchors by the shell lemma in `degree-five-disconnected.md`.
Replace `u,b,v` by `u`, that shell path, `v`.

In the one-fourth-layer route the marker is an endpoint adjacent to `u`.
Choose any anchor adjacent to `u` and any distinct anchor.  Use the shell
path between them, with its `u`-anchor endpoint followed by `u`, in place of
`b,u`.  The resulting path spans all of `G`.

Therefore every `(a,s)=(4,2)` extreme is traceable for `k>=7`.
