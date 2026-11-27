# Independent audit: two-anchor cover at a degree-three root

This audits `degree-three-two-anchor-order.md` under its stated hypotheses.
Write `A=N(z)`, `|A|=3`, and `L_i={x:d(z,x)=i}`; put `T=L_2` and
`d=k-|T|`.

## Layer and order accounting

Every anchor and every vertex outside `z` is high.  Hence the assumed
high-pair distance bound applies to an anchor `a` and any `y in L_5`:

```text
4 = d(z,y)-d(z,a) <= d(a,y) <= 4.
```

Thus every `L_5` vertex is a positive-even witness for every anchor.  The
same bound also gives `ecc(z)<=5`, so the layers displayed in the manuscript
exhaust the graph.

At `z`, every member of `T=L_2` and `L_4` is a positive-even witness.  These
sets are disjoint, so

```text
|T|+|L_4| <= k,      hence |L_4| <= d.          (1)
```

No high/low exception was used incorrectly here: `z` is the only vertex to
which the high-pair bound is not applied.

Suppose anchors `a,b` cover `T`.  Every `x in L_3` has a predecessor in `T`
on a shortest `z`--`x` path.  That predecessor sees `a` or `b`, so `x` is at
distance exactly two from at least one of them.

If one anchor is complete to `T`, it sees all of `L_3` at distance two and
all of `L_5` at distance four.  Therefore

```text
|L_3|+|L_5| <= k,
n = 4+|T|+|L_3|+|L_4|+|L_5| <= 2k+4.
```

Otherwise both covering anchors miss a member of `T`.

* If `ab` is absent, each anchor counts the other at distance two through
  `z`.
* If `ab` is present, choose `t_a in T\N(a)` and `t_b in T\N(b)`.  Covering
  forces `b t_a` and `a t_b`; hence `d(a,t_a)=d(b,t_b)=2`.  These witnesses
  are outside `L_3 union L_5` (and in fact are distinct, though distinctness
  across the two separate anchor budgets is not needed).

After reserving one witness in each anchor budget, summing the budgets counts
every `L_3` vertex at least once and every `L_5` vertex twice:

```text
|L_3|+2|L_5| <= 2k-2.                           (2)
```

Combining (1)--(2) gives

```text
n <= 4+|T|+(2k-2)+(k-|T|) = 3k+2.
```

The adjacent-anchor missed-`T` step is therefore valid, with no unspoken
assumption about whether a missed vertex is shared.

## Exact private-port residual above the order bound

If `n>3k+2`, no pair of anchors covers `T`.  For each anchor `i`, apply this
to the other two anchors: a `T` vertex missed by that pair must, by the
definition of `L_2`, be adjacent to `i`.  Hence it has anchor-neighborhood
exactly `{i}`.  Conversely, a private port for each anchor prevents every
two-anchor cover.  Thus the residual condition is exactly:

```text
each of the three masks 1, 2, 4 occurs in T.     (3)
```

The three selected private ports are distinct.  Let `a_i` be the degree of
anchor `i` in the three-vertex graph `G[A]`.  Every neighbor of `i` lies in
`{z} union A union T`; since `d(i)>=k`,

```text
|T\N(i)| <= |T|-(k-1-a_i) = 1+a_i-d.            (4)
```

The two other selected private ports already use two misses at `i`.
Consequently

```text
a_i >= 1+d,
```

for each anchor.  It follows exactly that

* `d=0` and `G[A]` is a path or a triangle; or
* `d=1` and `G[A]` is a triangle.

After the compulsory private masks, anchor `i` has residual miss budget
`a_i-1-d`.  Treating each remaining nonuniversal port mask by the set of
anchor seats it misses gives, up to anchor automorphism, exactly the nine
templates in the manuscript:

```text
path, d=0:      (1,2,4), (1,2,4,6);
triangle, d=1:  (1,2,4);
triangle, d=0:  (1,2,4), (1,1,2,4), (1,2,3,4),
                (1,1,2,4,6), (1,2,3,4,5),
                (1,2,3,4,5,6).
```

All omitted masks are universal mask `7`.  In the triangle with `d=0`, each
anchor has one free miss seat: an added double mask uses one seat, an added
private mask uses two, and admissible added masks must use disjoint seats.
This proves both completeness and nonduplication of the six listed forms.

Finally, eccentricity at least four makes `L_4` nonempty.  Equation (1) and
`d<=1` force `d=1` and `|L_4|=1`, hence the triangle template with exactly
one private port per anchor.  If `L_5` were nonempty, the unique `L_4` vertex
would separate it from `z`, contradicting 2-connectivity.  Therefore the only
non-eccentricity-three residual is the stated eccentricity-four singleton
`L_4` family.

**Audit conclusion.**  The two-anchor order theorem, all layer assertions,
the adjacent-anchor witness argument, the nine private-port templates, and
the eccentricity-four reduction are sound as written.
