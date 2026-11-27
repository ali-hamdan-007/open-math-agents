# Split graphs at connectivity three

Suppose G is a 3-connected split graph with clique Q, stable set I, and every
induced tree of order at most five. The published K₁,₄-free split graph theorem
handles one case. Otherwise an induced K₁,₄ has a center x in Q and at most one
leaf y in Q. If y exists, x has at least three neighbors in I. If x has
exactly three stable neighbors, they are the other leaves, and any stable
neighbor of y would induce a double star on six vertices. Thus y has no
stable neighbor and can move from Q to I. In all cases the graph admits a
split partition with some clique vertex u having four stable neighbors.

Write A for these four stable neighbors. For any other clique vertex v,
the edge uv and all private stable neighbors of its ends induce a double
star. The total number of private stable neighbors is therefore at most
three. Together with the bound of four stable neighbors for any clique
vertex, this gives at most one stable neighbor outside A for each clique
vertex, and at least two neighbors in A if there is an outside neighbor.
This implication is checked as `Graph199.split_full_row` in
`Graph199SplitStructure.lean`. In particular, the clique-neighborhoods
of the stable vertices outside A are disjoint and each has size at least
three.

## A bounded counterexample in the size-four-row case

Choose three clique neighbors of each vertex in $A$, including $u$ in
each choice. Mark the chosen clique vertices. There are at most ten marks
and at most nine are in outsider neighborhoods, since $u$ has no outsider
neighbor. Keep $A$, the marks, and all outsider vertices with a marked
neighbor. From each kept outsider's neighborhood, keep the marked neighbors
and add neighbors until at least three are kept. If originally there are two
or more outsiders, keep at least two in total, adding three neighbors for
each extra outsider.

The resulting clique has at most 28 vertices. To see this, let $q\le9$
be the number of marks other than $u$ and $g$ the number of outsider
neighborhoods containing a mark. Filling the $g$ marked groups adds at
most $2g$ vertices and the supplementary groups add
$3\max(0,2-g)$ vertices. The clique count is thus at most
$1+q+2g+3\max(0,2-g)\le28$. There are at most nine retained outsiders,
so the total order is at most 41.

When the original graph has exactly one outsider, keep that outsider and
three neighbors, regardless of marks. When it has at most one outsider,
add clique vertices if needed to reach a clique of size at least the stable
set, or keep the entire original clique when its size is less than that of
the stable set. These additions respect the 41-vertex bound.

The induced subgraph remains 3-connected: deletion of any two vertices
leaves a nonempty clique and every remaining stable vertex has a remaining
clique neighbor. It retains the row of size four and the induced-tree upper
bound. If at least two outsider groups were kept, the resulting clique
has size at least three times the number of kept outsiders and hence at
least the size of the stable set. In the other cases either the clique
has at least that size or the entire original graph was retained.

Assume the retained graph has a spanning path and has fewer vertices than
the original. Its clique has size at least its stable set, so the path has
either a clique endpoint or an adjacent pair of clique vertices. Each
omitted outsider and all its neighbors form a path with both ends in the
clique: place the outsider between two of its neighbors and order the
remaining vertices of that neighborhood after them. The neighborhoods are
disjoint. The other omitted clique vertices can be used as singleton paths.
Concatenate all such paths at the clique endpoint or between the adjacent
clique pair, recovering a spanning path of the original graph.

Thus a counterexample in this case would have an induced counterexample
on at most 41 vertices. This finite residual has not been exhausted.

## References

- Dai, Zhang, Broersma, and Zhang, “The Hamiltonian properties in
  \(K_{1,r}\)-free split graphs,” Discrete Mathematics (2022).
  https://doi.org/10.1016/j.disc.2022.112826
- Renjith and Sadagopan, “Hamiltonian Path in Split Graphs – a Dichotomy.”
  https://arxiv.org/abs/1711.09262

## Traceability with at least five outsiders

Give each outside vertex a demand of two distinct clique neighbors. Give
two vertices of A demand one, for the path endpoints, and the other two
demand two. All demanded neighbors must be distinct. Hall's theorem,
applied to two labeled copies of every vertex of demand two, tests whether
such an assignment exists.

For a subset X of A, write N(X) for its collective clique neighbors, and
write Q_s for an outsider's clique neighborhood. The minimum surplus
available to X over all subsets of outsiders is

```text
f(X) = |N(X) outside all groups|
       + sum over s of min(|N(X) intersect Q_s|, |Q_s| - 2).
```

Indeed, for one group, leaving its outsider outside the Hall subset
contributes the number of clique neighbors in the intersection. Including
the outsider contributes the whole group's size and subtracts its demand
of two. The groups are disjoint, so these choices minimize independently.
It suffices to check f(X) against the total demand of X. Hall subsets
containing only some copies of a selected vertex give weaker inequalities.

The original center u contributes to every nonempty X outside all groups.
For a singleton X, there is at least one other clique neighbor, contributing
at least one since every outsider group has at least three vertices.
For a subset X of size at least three, all group vertices have a neighbor
in X because each sees at least two of the four vertices of A. Thus f(X)
is at least one plus the number of groups, enough for any demand if there
are at least five groups.

If a group misses a pair X, each of its clique vertices sees exactly the
two vertices of A outside X. Within a group there is at most one such pair.
Two groups cannot miss different pairs. Choose a clique vertex in each
group. Their stable neighbor sets each consist of the corresponding
two-element complement in A and their respective outsider. Distinct pairs
would give at least four exclusive stable neighbors between the two clique
vertices, inducing a double star on at least six vertices. Consequently
there is at most one pair missed by any group. Give both members of that
pair demand one if it exists. Their pair has supply at least two by the
singleton bound and monotonicity. Every remaining pair is met by all
groups and again has supply at least one plus the number of groups.

The assignment supplied by Hall forms disjoint stable-centered blocks.
Every demand-two vertex lies between its two assigned clique neighbors.
The two demand-one blocks have a stable endpoint and a clique endpoint.
Place those blocks at the ends of the path and concatenate all other
blocks and unused clique vertices using clique edges. This is a spanning
path.

The remaining split case has at most four outside groups. The bounded
counterexample argument then keeps at most ten marked clique vertices,
at most eight additional clique vertices filling marked groups, and at
most eight stable vertices. If supplementary groups are needed to bring
the number to two, the number of added clique vertices is at most six
including filling marked groups. Thus the combined arguments give a
counterexample bound of 26 vertices.

## The four-group case

With four groups the same Hall argument works whenever f(A) is at least six.
Triples require at most five, and pairs other than the exceptional pair
are met by every group. If f(A) is less than six, every group has exactly
three clique vertices and u is the sole nongroup clique vertex seeing A.

For clique rows in different groups, their core neighbor sets differ in at
most one entry. The two distinct outsider neighbors already consume two of
the three allowed private leaves. If all core rows have size two, rows in
different groups must coincide. It follows that all rows coincide and two
core vertices have only one neighbor, which is impossible.

Otherwise select a size-three row P in one group S, and let a be the core
vertex missing from P. Any row outside S must be a subset of P, so the two
other rows of S must both contain a to give a three neighbors. Take any
row R in another group. It cannot have size three because it would have to
equal P and could not be within distance one of a row containing a. Thus
R is a pair contained in P, and both rows of S containing a must equal
R together with a. Every row in another group must be within distance one
of both distinct triples P and R together with a, so it must equal R. The
unique vertex of P outside R then has only two neighbors, u and the
clique vertex giving row P. This contradicts minimum degree three.

Thus at least four outsiders always suffice for the split graph to be
traceable. The witness construction now keeps at most ten marked clique
vertices and six further clique vertices, and at most seven stable
vertices. The row-u mark lies in no group, and the worst 23-vertex bound
requires six added clique vertices and three groups. This already reduces
the split residual to at most 23 vertices.
