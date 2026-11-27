# Adversarial audit of the eccentricity-four contradiction

This checks `degree-three-eccentricity-four.md` under the exact residual
provided by `degree-three-two-anchor-order.md`:

* `A={a_1,a_2,a_3}` is a triangle;
* `T=L_2` has the three private ports `p_i` and `W`, where every member of
  `W` sees all three anchors and `|W|=k-4`;
* `|T|=k-1`, `L_4={y}`, and `L_5` is empty;
* `C=L_3` has order `c=n-k-4>=2k-1`.

## Visibility count

For `V_i={x in C:d(a_i,x)=2}`, every length-two path from `a_i` to `C`
has a port as its middle vertex.  The two foreign private ports are also
positive even witnesses for `a_i`, through the anchor triangle, and are
outside `C`.  Hence

```
|V_i| <= k-2.                                           (1)
```

Every `C` vertex has a predecessor in `T`, so belongs to at least one
`V_i`.  If `U_i` denotes membership in exactly `V_i`, and
`U=U_1 union U_2 union U_3`, every vertex outside `U` contributes at least
two visibility incidences.  Therefore

```
sum_i |V_i| >= |U|+2(c-|U|)=2c-|U|,
|U| >= 2c-sum_i|V_i| >= k+4.                            (2)
```

No hidden disjointness beyond the disjoint definition of the `U_i` is
used here.

## A universal port touches at most one private port

Fix `w in W`.  A vertex in `U_i` can see no port except `p_i`: adjacency
to a foreign private port would put it in a foreign `V_j`, while adjacency
to a member of `W` would put it in all three `V_j`.

Thus, if `w` touched all three private ports, all of `U` would be at
distance two from `w`; together with `z`, this already exceeds the cap by
(2).

Suppose instead that `w` touches exactly two private ports and misses
`p_i`.  A vertex of `C` outside `U_i union B`, where
`B=V_1 intersect V_2 intersect V_3`, has no neighbor in `W` and has a
private-port neighbor different from `p_i`.  It is not adjacent to `w`,
and the foreign private port gives a length-two path from `w`.  These
`c-|U_i|-|B|` vertices, together with `z` and `p_i`, are distinct positive
even witnesses for `w`.  Hence

```
c-|U_i|-|B|+2 <= k,
c <= k-2+|U_i|+|B| <= k-2+|V_i| <= 2k-4,
```

contradicting `c>=2k-1`.  Therefore each `w in W` touches at most one of
the `p_i`.

## The `D_i` budgets

Put

```
R_i=N(p_i) intersect C,
D_i={x in C\\R_i : N(x) intersect R_i is nonempty},
b_i=|N(p_i) intersect W|.
```

Every member of `D_i` is at distance exactly two from `p_i`.  The following
additional witnesses are pairwise disjoint and lie outside `D_i`:

* the `|W|-b_i` common ports missed by `p_i`, through `a_i`;
* `z`, through `a_i`;
* the two foreign anchors, through the anchor triangle.

Thus

```
|D_i| <= k-(|W|-b_i)-3=b_i+1.                           (3)
```

Since every common port touches at most one private port,
`sum_i b_i<=|W|`, and (3) gives

```
sum_i |D_i| <= |W|+3=k-1.                               (4)
```

## Final cover of the exclusive vertices

Fix `x in U_i`.  Its only possible neighbors outside `C` are `p_i` and
`y`: it cannot see an anchor by the layer definition, and the port
observation above excludes all other ports.  Since `d(x)>=k`,

```
|N_C[x]| >= k-1.
```

By (1), this closed neighborhood is not contained in `V_i`; choose a
neighbor `u in C\\V_i`.  The vertex `u` has a port predecessor because it
lies in `L_3`.  That port is not a member of `W` (which would put `u` in
all `V_j`) and is not `p_i` (which would put `u` in `V_i`).  Hence it is
some `p_j`, `j != i`.  Thus `u in R_j`.  Meanwhile `x notin R_j`, because
`x in U_i`, and `xu` is an edge.  Therefore `x in D_j`.

This proves the set inclusion

```
U subseteq D_1 union D_2 union D_3.
```

It does **not** require choosing distinct images or proving an injection;
the ordinary union bound is exactly what is needed:

```
k+4 <= |U| <= |D_1 union D_2 union D_3|
             <= sum_i |D_i| <= k-1,
```

a contradiction.

## Audit conclusion

All witness sets in the cap counts are disjoint as claimed.  The visibility
count, the restriction on common-port/private-port incidences, the three
`D_i` budgets, and the final cover are valid.  No counterconfiguration
survives: the eccentricity-four residual is impossible.
