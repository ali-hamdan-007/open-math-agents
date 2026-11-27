# Adversarial audit of the clean triangle template at eccentricity three

I checked `degree-three-eccentricity-three-triangle.md` against the layer
definitions and the hypotheses in `degree-three-two-anchor-order.md`.  The
argument is sound for both deficits `d=0` and `d=1`.  In particular, the two
places most likely to hide an off-by-one error -- the witness counts and the
final cover of the exclusive set -- check exactly as written.

## Layer sizes and the exclusive-incidence lower bound

Here `|T|=k-d`, and the clean mask list consists of the three private ports
and `|W|=k-d-3` universal ports.  Since `n>3k+2` is integral,

```
c=|L_3|=n-4-(k-d) >= 2k+d-1.
```

For an anchor `a_i`, both foreign private ports are distinct positive
distance-two witnesses, via the two edges of the anchor triangle.  They lie
outside `C`, so the even-distance budget gives `|V_i|<=k-2` without overlap.
If `U` is the set of vertices having exactly one visibility incidence, then
every other `C` vertex has at least two.  Therefore

```
sum_i |V_i| >= |U|+2(c-|U|)=2c-|U|,
|U| >= 2c-sum_i|V_i| >= k+2d+4.
```

No equality direction is reversed here.

## A universal port cannot touch two private ports

An exclusive vertex in `U_i` cannot touch a universal port or a foreign
private port: either edge would give it visibility from another anchor.
Thus a universal port touching all three private ports has every member of
`U`, and also `z`, at distance exactly two.  The lower bound above already
exceeds the budget.

If a universal port `w` touches the two private ports foreign to `i`, a
vertex of `C\(U_i union B)` has a visibility set which is neither `{i}` nor
all three anchors.  In the clean mask template it consequently touches at
least one of those two foreign private ports.  It cannot touch `w`, since
that would make it triple-visible.  Hence all these vertices are genuine
distance-two witnesses for `w`.  The further witnesses `z` and the missed
private port `p_i` are distinct, giving

```
c-|U_i|-|B|+2 <= k.
```

Because `U_i` and `B` are disjoint subsets of `V_i`, this implies
`c<=2k-4`, contradicting `c>=2k+d-1`.  Thus each `w` contributes to at most
one of the three numbers `b_i`.

## The `D_i` count

Every `D_i` vertex is outside `R_i=N(p_i) intersect C` but adjacent to an
`R_i` vertex, so it is at distance exactly two from `p_i`.  Disjoint from
these are:

* the `|W|-b_i` universal ports missed by `p_i`, each at distance two through
  `a_i`;
* `z`, at distance two through `a_i`;
* the two foreign anchors, at distance two through `a_i` and the anchor
  triangle.

Therefore

```
|D_i| <= k-(|W|-b_i)-3=d+b_i.
```

Summing and using `sum_i b_i<=|W|` gives precisely

```
sum_i |D_i| <= 3d+|W|=k+2d-3.
```

This specializes to `k-3` when `d=0` and `k-1` when `d=1`; both values are
consistent with the corresponding port counts.

## Final cover of `U`

Fix `x in U_i`.  Eccentricity three eliminates a fourth layer.  Exclusivity
eliminates every second-layer neighbor except `p_i`, so `x` has at most one
neighbor outside `C`.  Since `x` is a high-degree vertex,

```
deg_C(x)>=k-1,  hence  |N_C[x]|>=k.
```

But `|V_i|<=k-2`, so a member `u` of `N_C[x]` lies outside `V_i`.  It is a
neighbor rather than `x` itself because `x in V_i`.  Every `C` vertex has a
second-layer predecessor.  A predecessor of `u` cannot be universal or
`p_i`, since either would put `u` in `V_i`; in this clean template it must
be a foreign private port `p_j`.  Hence `u in R_j`.  Exclusivity gives
`x notin R_j`, and the edge `xu` proves `x in D_j`.  Thus

```
U subseteq D_1 union D_2 union D_3.
```

Combining this cover with the two verified bounds yields the strict
seven-unit contradiction

```
k+2d+4 <= |U| <= sum_i |D_i| <= k+2d-3.
```

No additional connectivity, closure, or endpoint assumption is used in
this template elimination.
