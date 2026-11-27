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
