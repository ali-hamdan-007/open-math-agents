# The next `(a,s)=(3,3)` order: a rooted degree/incidence obstruction

Retain the degree-five-root notation.  Assume `(a,s)=(3,3)` and the first
remaining order

    h=|R|=2k-2.

Then `|K|=k-3`, there is no fourth layer, and

    D=P union R,  |P|=3,  |D|=2k+1.

Every vertex of `R` has all its neighbours in `D` and degree at least `k`.
This note gives a rooted closure at this order unless a precise two-level
degree obstruction occurs, and records the exact port-incidence restrictions
on that obstruction.

## A rooted Chvatal closure

By 2-connectivity the three ports collectively meet at least two distinct
anchors.  Hence there are ports `p,q` and assigned anchors `alpha~p`,
`beta~q` with `alpha != beta`.  Add a marker `b` adjacent only to `p,q`,
and call the resulting graph `H`.  Its order is

    N=2k+2.

The marker has degree two.  A selected port loses at most its five anchor
neighbours when restricted from `G` to `D`, and gains the marker, so its
degree in `H` is at least `k-4`.  The third port has degree at least `k-5`.
Every member of `R` has degree at least `k` in `H`.

Let

    d_1 <= ... <= d_N

be the degree sequence of `H`.  For `k>=9`, Chvatal's Hamilton-cycle
criterion is automatic at every index `i<N/2=k+1` except possibly `i=k`:

* `d_1=2>1`;
* `d_2>=k-5>=4>2`, while the two selected ports give
  `d_3,d_4>=k-4>=5`, so the indices two through four do not trigger;
* there are only four vertices outside `R`, hence `d_i>=k>i` for
  `5<=i<=k-1`.

At the sole remaining index, the criterion says

    d_k>k   or   d_(k+2)>=k+2.                 (1)

Whenever (1) holds, `H` has a Hamilton cycle.  Since `b` has exactly the
two neighbours `p,q`, deleting `b` from the cycle gives a Hamilton path of
`D` from `p` to `q`.  Join its endpoints through

    p-alpha, (the prescribed alpha--beta spanning shell path), beta-q.

This is a Hamilton cycle of `G`, and deleting any edge gives the required
Hamilton path.  Thus the endpoint construction is fully rooted; no
endpoint-preservation assertion about ordinary path closure is used.

Define the two low-degree sets in the residual core

    E_0  = {x in R : d_D(x)=k},
    E_01 = {x in R : d_D(x)<=k+1}.

If (1) fails, at least `k` vertices of `H` have degree at most `k`, and at
least `k+2` have degree at most `k+1`.  At most four of either collection
can lie outside `R`.  Therefore every counterexample at this order and
`k>=9` must satisfy

    |E_0|  >= k-4,                              (2)
    |E_01| >= k-2.                              (3)

Equivalently, either `|E_0|<=k-5` or `|E_01|<=k-3` closes the equality case
by the explicit marked Hamilton cycle above.

## Exact port-boundary restrictions

For a port `p`, put

    S_p=N_R(p),
    B_p={y in R-S_p : y has a neighbour in S_p}.

Every member of `B_p` is at distance exactly two from `p`.  Let `c_p` be
the number of the other two ports that are at distance exactly two from
`p`; these witnesses are distinct from `B_p`.

If `p` has at least two anchor neighbours, then it is at distance two from
all of `K` and from `z`.  These are `k-2` witnesses, so

    |B_p|+c_p <= 2.                             (4)

If the sole anchor of `p` is `alpha`, put

    m_alpha=|{x in K : x is not adjacent to alpha}|.

Then `p` sees `z` and the `k-3-m_alpha` members of `K` adjacent to `alpha`
at distance two, giving

    |B_p|+c_p <= 2+m_alpha.                     (5)

The five anchor defects satisfy

    sum_alpha m_alpha <= k-3.                   (6)

Finally, if `a_p` is the number of anchor neighbours of `p` and `e_p` its
degree in the three-port graph, then all neighbours of `p` are accounted
for by anchors, other ports, and `S_p`.  Its high degree therefore gives

    |S_p| >= k-a_p-e_p.                         (7)

Equations (2)--(7) are a finite obstruction at the first open order.  In
particular, a counterexample must simultaneously have a linear-size set of
exact-degree core vertices and three large attachment sets whose external
boundaries are bounded by the anchor-defect allocation.  The remaining
task is to route the exact-degree set through those finitely many port
incidence patterns; ordinary unrooted closure alone is insufficient because
it does not preserve a port endpoint.

For `k=7,8`, the same degree-sequence argument has additional possible
Chvatal triggers among the three port degrees; these are genuinely finite
small cases and are not claimed closed here.

## Cycle-closure sharpening for `k>=11`

The preceding obstruction can be made considerably more rigid.  Fix ports
`p,q` with distinct assigned anchors and add the edge `pq` if it is absent.
Call this graph `J`.  It has order `2k+1`.  Apply ordinary Hamilton-cycle
closure, whose threshold is `2k+1`, to missing pairs inside `R`.

Let `L` be the vertices of `R` which finish this process still at their
original degree `k`, and put `U=R-L`.  Every member of `U` becomes complete
to `R`, while every member of `L` was already adjacent in the original
graph to every member of `U`: a missing `L-U` edge has degree sum at least
`k+(k+1)=2k+1` and would be inserted, raising the degree of its `L` endpoint.
Thus the closed core has the form

    K_|U| join G[L],

and all `L-U` edges are original edges.

Suppose first that `l=|L|<=k-2`.  Then

    u=|U|=2k-2-l >= l+2.                       (8)

Every port has at least

    k-5-2=k-7

neighbours in `R`: it loses at most five anchor neighbours and has at most
two port neighbours.  For `k>=11` each of the three port neighbourhoods in
`R` therefore has at least four members.  Hall's theorem with demands
`(1,1,2)` gives four distinct contacts

    a in N_R(q),  d in N_R(p),  b,c in N_R(t),

where `t` is the third port.  Indeed, each single neighbourhood has size at
least four, so every union meets the sum of the relevant demands.

There is an elementary spanning ordering of the closed core from `a` to
`d` containing the prescribed block `b,t,c`.  Order the vertices of the
clique `U` so that those among `a,b,c,d` occur in the required order, with
`a` first or `d` last when either belongs to `U`.  The ordered `U` list has
`u+1` gaps.  Insert the vertices of `L` into distinct gaps, putting `a` in
the first gap or `d` in the last when appropriate.  Make `b,c` consecutive
in the resulting core order: if both lie in `U`, use consecutive positions
of the `U` list and leave their intervening gap empty; if exactly one lies
in `L`, put it in the gap immediately next to the other; if both lie in
`L`, put them in the same gap in the order `b,c`.  Replace that one formal
adjacency by `b,t,c`.  The remaining `L` vertices occupy arbitrary unused
gaps.  Since `u>=l+2`, at least three more gaps than `L` vertices are
available, so all endpoint and empty-gap requirements can be met.  Every
other consecutive pair either lies in `U` or crosses the complete `U-L`
join.

Adding the edge `p-q` to the ends gives the Hamilton cycle

    p,q,a, (all of R with the block b,t,c), d,p

of the closed `J`.  Reverse the cycle-closure steps, obtaining a Hamilton
cycle `C` of `J`.  If `pq` was artificially added and `C` uses it, replace
that edge by the prescribed shell path between the distinct assigned
anchors of `p,q`.  If `C` avoids an artificial `pq`, then it is already a
Hamilton cycle of `D`; break a port-incident edge and append a prescribed
shell path there.  Use the same latter construction when `pq` was original.
Hence a
counterexample for `k>=11` must satisfy

    |L| >= k-1.                                 (9)

## Exact incidence on the surviving set

Assume (9) and write `l=|L|`, `u=2k-2-l`.  As long as `u>0`, any two
vertices of `L` have a common original neighbour in `U`.  For `x in L`, let
`t_x` be the number of its port neighbours.  Since every third-layer vertex
has a port neighbour, `1<=t_x<=3`, and exact degree gives

    d_L(x)=k-u-t_x=l-k+2-t_x.                  (10)

Thus `x` has exactly `k-3+t_x` nonneighbours in `L`.  All of them are at
distance two from `x` through `U`.  In addition, every anchor adjacent to
one of the `t_x` port neighbours is at distance two from `x`.  If `A_x` is
the union of those anchor sets, the even-distance cap gives

    (k-3+t_x)+|A_x| <= k,
    t_x+|A_x| <= 3.                            (11)

Consequently:

* no member of `L` is adjacent to all three ports;
* a member adjacent to two ports can exist only when both ports have the
  same sole anchor;
* a member adjacent to one port can use only a port having at most two
  anchor neighbours.

Because the entire component must use at least two distinct anchors, at
most one pair of ports can support the double-incidence type in the second
bullet.  Equations (9)--(11) reduce the open equality case to the following
finite split-core obstruction.  Write `l=k-1+c`, so `u=k-1-c`.  The
untouched set `L` is joined completely to the universal clique `U`; each
of its vertices has one of at most four port-incidence types (three
singletons and, possibly, one same-anchor pair), and its degree inside `L`
is exactly

    c       for a singleton type,
    c-1     for the possible double type.       (12)

This is stronger than the raw Chvatal counts: every case outside the rigid
family (9)--(12) has the explicit rooted spanning construction above.  The
endpoint problem that remains is now purely the path-cover problem for the
finite incidence types in (12), with the `k-1-c` universal vertices as
separators.

There is no numerical path-cover deficit in this last problem.  From (12),

    delta(G[L]) >= c-1.

Adjoin `u+2=k+1-c` new universal vertices to `G[L]`.  The resulting graph
has order

    (k-1+c)+(k+1-c)=2k,

and every old vertex has degree at least

    (c-1)+(k+1-c)=k.

Dirac's theorem gives a Hamilton cycle.  Removing the new universal
vertices cuts it into at most `u+2` disjoint paths covering `L`.  Hence

    path_cover_number(G[L]) <= u+2.            (13)

The `u` genuine universal vertices join all but two of these paths.  The
two remaining joins are exactly the available port gadgets: the selected
shell pair joined by the temporary `pq` edge acts as one connector, and the
third port acts as the other.  What still requires proof is the *coloured
endpoint* version of (13): the two exceptional path joins must have endpoint
colours matching those port gadgets.  Equations (11)--(12) show that there
are only the three singleton colours and at most one same-anchor double
colour.  Thus the residual is not an unbounded graph-theoretic search, but
one precise coloured path-cover lemma.  No claim that uncoloured (13) alone
settles the endpoint assignment is made here.

## The first two split layers close for `k>=11`

For a path rooted at one port `p`, the other two ports `q,r` will be used as
two internal connectors.  We need distinct contacts with demands

    (1,2,2) on (N_R(p),N_R(q),N_R(r)).          (14)

Each port has at least `k-7` core neighbours.  For `k>=11`, Hall can fail
in (14) only if the union of all three core neighbourhoods has order four;
then all three neighbourhoods equal the same four-set `S`.

This exceptional equality is impossible already for `k>=11`.  Indeed, a member of
`S` has only the other three members of `S` and the three ports available
before leaving `S`, so its degree forces at least `k-6` vertices in the
external boundary of `S`.  That whole boundary is at distance two from
each port.  A port with at least two anchors has only two residual even
slots, impossible here.  Thus all three ports have sole anchors.  Such a
port has at most two port neighbours, so its degree bound gives

    |N_R(p)| >= k-1-2=k-3.

The common neighbourhood has order four, forcing `k<=7`, a contradiction.
Therefore (14) has distinct representatives for every `k>=11`.

Choose contacts

    a~p,  b,c~q,  d,e~r

as in (14), choosing `a` in `L` whenever `p` has an `L`-neighbour.  This
preassignment is compatible with Hall: after deleting `a`, the two other
neighbourhoods still satisfy the demands `(2,2)`.  Indeed, the only new
failure would make those two original neighbourhoods the same four-set.
Its external boundary has at least `k-6` vertices at distance two from both
ports, by the same degree count used above.  A port with at least two
anchors has only two residual even slots, while a sole-anchor port with
only four core neighbours has total degree at most `1+2+4=7`; both are
impossible for `k>=11`.  We seek a spanning path of `D`
beginning at `p,a`; the formal
core adjacencies `b-c` and `d-e` may be replaced by the genuine blocks
`b-q-c` and `d-r-e`.

If `c=0` in (12), then `|L|=|U|=k-1`, every member of `L` has singleton
port type, and `L` is independent.  The following elementary gap count
makes the endpoint choice precise.  An internal port whose colour class in
`L` has size at least two can be used as an `L-port-L` block; call this an
`LL` reduction.  A port with empty colour class is forced to be a
`U-port-U` block; call this a `UU` cost.  A singleton colour class permits a
mixed block and has zero balance.  If the rooted first contact is in `U`, a
spanning `U/L` ordering exists whenever the number of `LL` reductions is at
least the number of `UU` costs; take the free endpoint in `L`.  If the first
contact is in `L`, one additional `UU` cost is harmless.  This follows by
putting each `L`-run in a distinct gap of the ordered clique `U`, putting
two `U` vertices in each gap carrying a `UU` block, and putting surplus `U`
vertices consecutively.

If some port has empty `L`-colour class, choose one such port as the root.
Among the two internal ports there is then at most one `UU` cost, and some
other colour class has size at least two, supplying an `LL` reduction.  If
no colour class is empty, root at an `L` contact; neither internal port is
forced to incur a `UU` cost.  Thus the gap balance always holds.  Arrange
the five distinct contacts in the resulting order and replace the two
formal contact pairs by the genuine internal-port blocks.  Prefixing the
root port gives a port-rooted spanning path of `D`, to which the shell path
is appended.

If `c=1`, then `|L|=k` and `|U|=k-2`.  By (12), singleton-type vertices
have degree one in `L`, while double-type vertices have degree zero.
Consequently the singleton vertices form a perfect matching on their
support and the double vertices are isolated.  Now `|U|=|L|-2`.  The same
gap count says that `LL reductions - UU costs` must be at least one when the
root contact lies in `L`, and at least two when it lies in `U`.  Matching
edges count as additional disjoint `LL` reductions.

If every port has an `L`-neighbour, root at an `L` contact.  There is no
forced `UU` cost, and either the singleton matching has an edge or some
double type is present and its two incident ports can supply an
`L-port-L` block.  Thus the required balance one is available.

If a port has no `L`-neighbour, use it as the root.  All vertices of `L`
then use the other two colours.  If there are at least two singleton
matching edges, use them.  With at most one matching edge, all but at most
two vertices have the common double type; since `|L|=k>=11`, both remaining
ports have ample distinct double-type contacts and their two port blocks
supply the two reductions.  If a second port also has empty colour class,
the last port contains every singleton colour; use its `L-port-L` block and
two disjoint edges of the large singleton matching, offsetting the one
forced `UU` block.  In each case the balance is at least two, and the
universal vertices separate all remaining `L` runs.  The rooted shell
splice again finishes the spanning path.

The preceding `c=0,1` constructions were written in the selectively closed
core.  Their rooted reversal is justified as follows, and the same device
applies to the `c=2` construction below.  Adjoin a new leaf `ell` at the root
port `p`.  The augmented graph has order `2k+2`, so Hamilton-path closure has
threshold `2k+1`, exactly the threshold used for the core edges inside `R`.
Reverse those closure steps in the augmented graph.  The leaf `ell` remains
a degree-one endpoint throughout; deleting it therefore leaves a spanning
path of the original `D` rooted at `p`.  The shell splice is consequently
made using only original edges.

Thus for `k>=11` a counterexample in the rigid family must have

    c>=2,  equivalently |L|>=k+1.               (15)

The smaller values `k<=10` require their own contact count; no claim about
them is made in this section.

## The layer `c=2` also closes for `k>=11`

When `c=2`, equation (12) says that singleton-type vertices have degree two
in `G[L]`, while double-type vertices have degree one.  Hence `G[L]` is a
disjoint union of cycles and paths; the degree-one vertices are precisely
the endpoints of the path components.  Break each cycle at one edge.  This
gives a path cover with

    r <= floor(|L|/2)=floor((k+1)/2)             (16)

paths, since every component has at least two vertices.

Use the five distinct contacts from (14).  First suppose `a` lies in `L`.
To expose it as an endpoint of its cover path costs at most one additional
path (delete one incident cover edge if it is internal).  To insert an internal port at
contacts `b,c`, expose the two contacts by at most two cuts and then join
the two selected pieces through `b-port-c`; the net increase in the number
of cover paths is at most one.  The same holds for the second internal
port.  We therefore obtain a path cover of all of `L` and all three ports
with at most

    r+3

members, one of which has the chosen root port as an endpoint.  Every other
path endpoint lies in `L`.

Here `|U|=k-3`, and for `k>=11`,

    k-3 >= floor((k+1)/2)+2 >= (r+3)-1.

Use distinct vertices of the universal clique `U` to concatenate the cover
paths, beginning with the root-port path.  Put any unused `U` vertices
consecutively in one join.  The result is a spanning path of `D` rooted at
the chosen port, and the shell splice completes a spanning path of `G`.

If instead `a` lies in `U`, do not spend the root-exposure cut.  The two
internal ports leave at most `r+2` cover paths.  Start with `p-a`, use `a`
to enter the first path, and use one further universal vertex between each
successive pair of paths.  This consumes at most

    r+2 <= floor((k+1)/2)+2 <= k-3=|U|

vertices of `U`, and again produces the required rooted spanning path.

Consequently the rigid obstruction for `k>=11` now satisfies

    c>=3,  equivalently |L|>=k+2.               (17)
