# The three-private triangle template is impossible at high order

Assume the hypotheses of `degree-three-two-anchor-order.md`, with `G`
2-connected and `n>3k+2`.  Let `z` have eccentricity three.  Consider the
triangle-anchor templates in which the only nonuniversal port masks are

```
(1,2,4).
```

Thus the anchors `A={a_1,a_2,a_3}` induce a triangle, there is one private
port `p_i` for each anchor, and all other ports form a set `W` adjacent to
all three anchors.  Put

```
T=L_2,  |T|=k-d,  d in {0,1},  |W|=k-d-3,
C=L_3,  c=|C|=n-4-(k-d)>=2k+d-1.
```

The case `d=0` is the first triangle template in the six-mask list.  The
case `d=1` is the unique triangle template at that deficit.  We prove that
neither can occur.

For each `i`, let

```
V_i={x in C : d(a_i,x)=2},
U_i=V_i\(V_j union V_l),
U=U_1 union U_2 union U_3,
B=V_1 intersect V_2 intersect V_3.
```

The two foreign private ports are positive even witnesses for `a_i`, so

```
|V_i|<=k-2.                                             (1)
```

Every `C` vertex has a port predecessor and belongs to at least one `V_i`.
Every vertex outside `U` contributes at least two visibility incidences.
Consequently

```
|U| >= 2c-sum_i|V_i| >= k+2d+4.                        (2)
```

We next show that a common port `w in W` touches at most one private port.
A vertex of `U_i` has no port neighbor except `p_i`: a foreign private
neighbor creates foreign visibility, and a common-port neighbor creates
triple visibility.  If `w` touched all three private ports, all of `U` and
also `z` would be positive even witnesses for `w`, contradicting (2).

If `w` touched exactly two private ports and missed `p_i`, every vertex of
`C\(U_i union B)` has a foreign private-port neighbor touched by `w`, and
has no common-port neighbor.  Hence all these vertices are at distance two
from `w`.  The vertices `z` and `p_i` are two further witnesses, giving

```
c-|U_i|-|B|+2<=k,
c<=k-2+|U_i|+|B|<=k-2+|V_i|<=2k-4,
```

contrary to `c>=2k+d-1`.  Thus each common port touches at most one private.

For each `i`, put

```
R_i=N(p_i) intersect C,
D_i={x in C\R_i : N(x) intersect R_i is nonempty},
b_i=|N(p_i) intersect W|.
```

Every member of `D_i` is at distance two from `p_i`.  Disjoint additional
positive even witnesses are the `|W|-b_i` common ports missed by `p_i`,
the vertex `z`, and the two foreign anchors.  Therefore

```
|D_i|<=k-(|W|-b_i)-3=d+b_i.
```

Since each member of `W` touches at most one private,

```
sum_i|D_i|<=3d+sum_i b_i<=3d+|W|=k+2d-3.               (3)
```

Finally fix `x in U_i`.  Its only neighbor outside `C` is `p_i`, because
there is no fourth layer and no other port is available to it.  Hence
`d_C(x)>=k-1` and `|N_C[x]|>=k`.  By (1), this closed neighborhood is not
contained in `V_i`; choose a neighbor `u in C\V_i`.  A port predecessor of
`u` is neither common nor `p_i`, so it is `p_j` for some `j != i`.  Thus
`u in R_j`, while `x notin R_j`, and the edge `xu` proves `x in D_j`.
Accordingly

```
U subseteq D_1 union D_2 union D_3.
```

Combining (2), the union bound, and (3) yields

```
k+2d+4 <= |U| <= sum_i|D_i| <= k+2d-3,
```

the desired contradiction.  Hence neither clean three-private
triangle-anchor template survives at eccentricity three.
