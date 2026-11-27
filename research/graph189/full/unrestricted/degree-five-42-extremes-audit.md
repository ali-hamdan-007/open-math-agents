# Independent audit of the `(a,s)=(4,2)` extremes

This checks `degree-five-42-extremes.md` under the notation of
`degree-five-disconnected.md`.

## Structural equalities

Here `|K|=k-4`. A vertex of `K` has only the other `k-5` members of `K` and
the five anchors available as neighbors. Its degree is at least `k`, so all
those `k` possible edges occur. Hence `K` is a clique complete to the anchor
set. For either port, `z` and `K` are therefore `k-3` distinct exact
distance-two witnesses.

The previously established bounds `|N_R(u)|,|N_R(v)|<=k-1` and disjointness
of the nonempty port-anchor sets apply without change.

For one fourth-layer vertex and `|D|=2k+1`, order equality forces disjoint
sets `U,V`, each of order `k-1`. The fourth-layer vertex meets both sides.
At `u`, the witnesses `z,K,f` leave two even-distance slots, so at most two
vertices of `V` can be endpoints of cross edges from `U`. Thus
`delta(U),delta(V)>=k-4`; since the sides have order `k-1`, Dirac applies for
`k>=7`. Opening the two cycles at chosen neighbors of `f` gives the displayed
spanning path of `D+b`. All endpoint adjacencies are valid.

For two fourth-layer vertices, the order and port-neighborhood bounds imply
exactly the side-size alternatives in the manuscript: either disjoint sides
of orders `(k-1,k-1)` or `(k-1,k-2)`, or a one-point intersection of two
`(k-1)` sets. The proof that `uv` is absent is valid: after discarding the
possible common member, at least `k-2` vertices of the opposite
port-neighborhood would be at distance two, in addition to `z` and `K`,
exceeding the cap for `k>=6`.

## One-point-intersection bookkeeping

There is a minor imprecision in lines 82--104, but the claimed minimum-degree
bound remains correct. Let `w` be the unique common port-neighbor and assign
it to `X`, so `Y=V\{w}`. At `u`, all members of `F_X` and all cross endpoints
`E_Y` are exact distance-two witnesses, and `v` is one more witness through
`w`. Consequently

```text
|F_X|+|E_Y|+1 <= 3.
```

For `x=w`, the possible outside-`X` neighbors are `u,v,F_X,E_Y`; for every
other `x` they are `u,F_X,E_Y`. In both cases there are at most four, so
`delta(X)>=k-4`.

The formally symmetric displayed inequality need not hold verbatim for the
fixed partition: a cross endpoint in `X` may be `w`, which is adjacent to
`v` and hence is not an exact distance-two witness from `v`. The correct
count is

```text
|F_Y| + |E_X\{w}| + 1 <= 3,
```

where the final witness is `u` via `w`. If `w in E_X`, this gives
`|F_Y|+|E_X|<=3`; if not, it gives the stronger bound at most two. Since a
vertex of `Y` has outside neighbors only among `v,F_Y,E_X`, it again has at
most four, and `delta(Y)>=k-4`. Thus the manuscript's conclusion is sound,
but “the symmetric argument” should use this corrected count.

For sides of order at most `k-1`, minimum degree `k-4` meets Dirac's threshold
for `k>=7`: for order `k-1`, `k-4 >= (k-1)/2` exactly when `k>=7`, and the
order-`k-2` threshold is weaker. Therefore both side cycles used later exist.

## Placement of the fourth-layer pair and shell expansion

Each fourth-layer vertex has a side-neighbor because its only alternative
outside `R` is the other fourth-layer vertex. If their two-by-two incidence
graph with the sides has a matching, assigning them to different sides and
opening the side cycles gives exactly the displayed path. If there is no
matching, both have neighbors only in one side. The chain

```text
k <= d(h) <= |X|+1 <= k
```

forces equality throughout, so `|X|=k-1`, the fourth-layer pair is adjacent,
and both are complete to `X`; the second displayed path is then valid.

Finally, the marker positions are as stated: internal between `u,v` in the
two-fourth-layer routes and an endpoint beside `u` in the one-fourth-layer
route. For `a=4`, the marked shell has order `k+3`; a `K` vertex and an
anchor have shell degrees at least `k` and `k-2`, whose sum reaches the cycle
closure threshold for `k>=5`. Since `|K|=k-4>=3` at `k>=7`, the explicit
anchor-to-anchor shell cycle construction has enough distinct `K` vertices.
The disjoint port-anchor sets provide distinct splice endpoints.

**Audit conclusion.** The `(4,2)` extremes are traceable for every `k>=7`
as claimed. The only correction needed is the explicit one-point-intersection
count above; it does not weaken `delta(X),delta(Y)>=k-4` or any subsequent
route.
