# Independent audit: bounded common-middle degree

Audited source SHA-256:

```text
d7d9f4304ed8354956c7e30c6f85b02b5d889cbffc4d9f0859538d25c38707e5
```

Let `d=max_t |N_W(t)|`.  If the earlier `k>=7h+84` theorem does not apply,
then the manuscript correctly derives

```text
2h>3d+13,       2h<=k-6.
```

With `D=k-d-e`, every remote has internal degree at least `D`, and the
visibility bound gives `c+2<=3D`.

## Hamiltonicity of a 2-connected remote layer

For an independent set of size `D+1`, every pair has a common original
remote neighbor because `c-|I|<=2D-3`.  If a member saw `W`, then through a
chosen `W` neighbor it would see at least
`k-e-d-h-2` other common middles at distance two.  Together with three
anchors and the `D` independent peers this exceeds the even-distance cap.
Thus every member has no `W` neighbor and has closed remote neighborhood at
least `k-e+1`.

At an exceptional support, the common `W` neighbors, one anchor, and the
independent peers give `a_J<=d+e-1`.  Combining the support-boundary bound
with the closed-neighborhood packing yields

```text
|I intersect S_J| <= d+3e-5.
```

The `e` supports cannot cover `I` under
`k>=(e+1)d+3e^2-4e`, which is implied by `k>=11d+130` for `e<=6`.
Therefore `alpha(R)<=D`; since `3D>=c+2`, Nash--Williams gives a Hamilton
cycle whenever `R` is 2-connected.

## Disconnected and cut layers

The component sizes are at least `D+1` when disconnected and at least `D`
after deleting a cut vertex.  Since `c<=3D-2`, exactly two parts remain.
Each part has order at most `2D-3` and internal minimum degree at least
`D-1`, so a degree-two endpoint marker and selective cycle closure give
Hamilton-connectedness with arbitrary specified original endpoints.

Each part contains a nontriple because `D>h`.  Across both parts there are
more than `k-h-2` nontriples, while an anchor-visible nontriple class and an
exceptional nontriple support each have size at most `k-h-2`.  This validates
the distinct-anchor/distinct-port selection, including the repair when the
first choices use one common port.  The cut vertex is incorporated by a
spanning path between two of its neighbors in one part; the other part has
its own cycle.

## Insertions and the outer `W` path

An unreserved exceptional port with `a_J<=e` has at least
`k-a_J-e-1` remote neighbors and remote boundary at most `a_J+e-2`.
It therefore has at least `k-4e+1>=e-1` eligible original cycle edges, enough
for greedy distinct subdivision.  Every remaining unreserved port has at
least `e+1` `W` neighbors.

For the graph on `W` and these high ports, with an endpoint marker, the order
is at most `k`.  If `mu(w)` is the number of missed `W` peers and `t(w)` its
triple degree, ambient degree counting gives

```text
mu(w)<=t(w)+2,
max mu<=h+2<=k/2-1,
sum mu<=hd+2|W|.
```

A `W` pair qualifies at cycle-closure threshold whenever its missed-count
sum is at most `k-2e-2`.  First complete every vertex with original
`mu<=k/3`; the inequality against the maximum miss is valid for
`k>=130,e<=6`.  Fewer than `3hd/k+6<=3d/2+6` vertices remain.  Once all low
vertices are complete, only these can be mutually missed, so any two
remaining miss counts sum to less than `3d+12<=k-2e-2`.  Thus closure makes
`W` a clique.

Each high port then qualifies against every `W` vertex, since its degree is
at least `e+1` and a clique `W` vertex has degree at least `k-e-1`.  The at
most `e-1` ports fit in distinct gaps of a `W` spanning path with the chosen
marker endpoints.  Reversing selective closure and deleting the untouched
marker yields an original path with those prescribed `W` endpoints.

The final one-cycle and two-cycle concatenations use explicit reserved
ports, distinct anchors, the root frame, and opened remote cycles, covering
every vertex exactly once.

**Audit conclusion.**  The remote degree/independence argument, independent-
triple Hamiltonicity criterion, disconnected/cut routing, summed `W`-deficit
closure, constants, and endpoint assembly are sound under `k>=11d+130`.
No endpoint-preservation assumption is hidden.
