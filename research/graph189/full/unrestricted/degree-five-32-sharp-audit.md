# Audit and sharpening of the extreme `(a,s)=(3,2)` case

This note independently checks lines 97--126 of
`degree-five-disconnected.md` and sharpens the argument.  It uses the notation
of that file.  Thus

* `A=N(z)` is the five-element anchor set;
* `K` has order `k-3`;
* `u,v` are the two ports;
* `U=N_C(u)` and `V=N_C(v)` are disjoint and both have order `k-1`;
* `f` is the unique fourth-layer vertex; and
* the anchor sets `A_u=N_A(u)` and `A_v=N_A(v)` are nonempty and disjoint.

Put `h_u=|A_u|` and `h_v=|A_v|`.  In particular

```text
h_u,h_v >= 1,             h_u+h_v <= 5.
```

The vertex `f` has a neighbor on each side.  Indeed, if it missed (say) `U`,
then all its neighbors would lie in `V`, which has only `k-1` vertices,
contrary to `d(f)>=k`.

## Exact cross-endpoint bound

Let `Y` be the set of vertices of `V` incident with a `U`--`V` edge.  Choose
`alpha in A_u`.  Split the anchor neighbors of `alpha`, other than `alpha`
itself, into

* `t_in` neighbors in `A_u`, and
* `t_out` neighbors in `A\A_u`.

The only possible neighbors of `alpha` are `z,u,K`, and other anchors.  (An
edge to any deeper-layer vertex would contradict its layer, an edge to `v`
would put `alpha` in both disjoint port-anchor sets, and an edge to `K` is
already counted.)  Hence

```text
d_K(alpha)+t_in+t_out+2 >= k.
```

Since `t_in <= h_u-1`, this gives

```text
d_K(alpha)+t_out >= k-h_u-1.                 (1)
```

The following are pairwise disjoint distance-two witnesses from `u`:

```text
z, f, N_K(alpha), the t_out anchors, and Y.
```

Here `f` is reached through a neighbor in `U`, and every member of `Y` is
reached through its incident endpoint in `U`.  None of the listed vertices is
adjacent to `u`, by the layer definitions and the definition of `A_u`.
The distance-two cap at `u`, together with (1), therefore gives

```text
2+d_K(alpha)+t_out+|Y| <= k,
|Y| <= h_u-1.                                  (2)
```

Symmetrically, if `X` is the set of vertices of `U` incident with a
`U`--`V` edge, then

```text
|X| <= h_v-1.                                  (3)
```

Every vertex of `U` has no neighbor outside `U` except possibly `u,f`, and a
member of `Y`.  Thus (2) yields

```text
delta(G[U]) >= k-h_u-1.                        (4)
```

Likewise

```text
delta(G[V]) >= k-h_v-1.                        (5)
```

This refines the manuscript's uniform `k-6` estimate.  It also confirms that
the original `|Y|<=4` and `delta>=k-6` estimates are valid, so the published
`k>=12` closure has no gap.

## Closure for every `k>=7`

There are two cases.

### Neither anchor set has size four

Here `h_u,h_v<=3`.  From (4)--(5), both induced graphs, each of order `k-1`,
have minimum degree at least `k-4`.  For `k>=7`,

```text
k-4 >= (k-1)/2.
```

Dirac's theorem gives a Hamilton cycle in each of `G[U]` and `G[V]`.
Choose `x in N(f) intersect U` and `y in N(f) intersect V`.  Open the two
cycles at an edge incident with `x`, respectively `y`.  This gives a spanning
path of `U` with endpoint `x`, and a spanning path of `V` with endpoint `y`.
Orient their other endpoints toward the ports.  Then

```text
u -- (all of U) -- x -- f -- y -- (all of V) -- v
```

is a Hamilton `u`--`v` path of `D`.

### One anchor set has size four

After interchanging the ports, `(h_u,h_v)=(4,1)`.  Formula (3) gives `X` empty,
so there are no `U`--`V` cross edges at all.  A vertex of `U` has possible
neighbors only in `U`, together with `u` and `f`.  Since `|U|=k-1`, omitting
`f` would give it degree at most

```text
(k-2)+1=k-1,
```

which is impossible.  Thus every vertex of `U` is adjacent to `f`; its degree
condition then also forces all `k-2` possible neighbors in `U`.  Hence `U` is
a clique and `f` is complete to it.  The identical argument applies to `V`.
The displayed Hamilton `u`--`v` path follows immediately.

This also disposes of the only apparent skew residue for `k=7,8`.  Therefore
the extreme `(a,s)=(3,2)` case is traceable for every `k>=7`, not merely for
`k>=12` (or `k>=9`).

## Shell splice audit

For completeness, in this case `|K|=k-3`.  After adjoining the degree-two
endpoint marker, the shell has order `k+4`.  A `K` vertex has shell degree at
least `k`, and an anchor has shell degree at least `k-2`.  Thus every missing
anchor--`K` edge has degree sum at least

```text
2k-2 >= k+4
```

already for `k>=6`.  Cycle closure therefore supports exactly the prescribed
anchor-to-anchor spanning shell path used in the manuscript.  Since the two
port-anchor sets are nonempty and disjoint, the two endpoints selected for
the splice are distinct.  Replacing the appropriate marker segment by this
shell path yields a spanning path of the whole graph.

**Audit conclusion.**  All neighborhood, distance-two, closure, and splice
claims in the manuscript's `(3,2)` extreme argument are sound.  The sharper
cross-endpoint accounting above closes the case for the full standing range
`k>=7`.
