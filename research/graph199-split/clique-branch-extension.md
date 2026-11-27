# Nonsplit clique branches at connectivity three

Let G be a 3-connected graph in which every induced tree has at most five
vertices. Suppose a clique Q separates the graph into at least two components
and each component C of G − Q is a clique. Assume the following attachments.

- Each component C has a representative adjacent to every vertex of Q that
  has a neighbor in C.
- If C has at least two vertices, every vertex of Q that meets C has at least
  two neighbors in C.

Then G has a spanning path, by the split-graph result and the following lift.
The representative vertices together with Q induce a split graph. The
neighborhood of each component in Q has at least three vertices, since
deleting that neighborhood would separate the component from another
component. The split graph is therefore 3-connected. Deleting any two
vertices leaves a nonempty clique and each remaining representative sees
at least one remaining clique vertex. It inherits the induced-tree bound
from G, so it has a spanning path.

The representative vertices form a stable set. For any representative in
the interior of the path, its predecessor and successor belong to Q.
If the component is a singleton, keep the representative. Otherwise
choose distinct vertices of the component adjacent to the predecessor
and successor respectively. Each has at least two choices, so a distinct
pair exists. A complete graph has a spanning path between any distinct
endpoints, so replace the representative by this path. At either end of
the quotient path choose one attachment and list the rest of its component
before or after it as appropriate. This spans all of G.

The uniform-attachment special case requires only that the quotient have
a spanning path. The lift through clique fibers, with complete joins on
quotient edges, is kernel-checked as
`Graph199.hamiltonian_of_clique_quotient` in `Graph199CliqueQuotient.lean`.

## Example with an induced four-cycle

The clique Q consists of disjoint triples X, Y and Z. Outside Q, there
are four singletons a, b, d, e and a three-vertex clique C. Both a and b see
all of Q. Vertex d sees precisely Y, and e sees precisely Z. In C, vertex
c₀ sees all three members of X, c₁ sees x₁ and x₃, and c₂ sees only x₂.
There are no other external edges. Vertices x₁, x₂, c₁ and c₂ induce a
four-cycle, so the graph is nonsplit.

Deleting at most two vertices leaves a connected graph. For C this follows
from the three disjoint attachment edges x₁c₁, x₂c₂ and x₃c₀. The singleton
d has degree three, so the connectivity is exactly three. The independence
number is five by taking one vertex per outside component. Any independent
set meeting Q excludes both a and b, and none contains two Q vertices.
The complement is connected because the complement on the outside components
is complete multipartite and every Q vertex misses some outside vertex.

An induced tree contains at most two Q vertices. Without Q vertices it
lies in one clique and has order at most two. With one Q vertex the tree
can include at most a and b, along with one outside branch of order at
most two. With two Q vertices the triangles through a and b exclude both
of them. At most two outside branches meet the chosen Q vertices, and
only C can contribute two vertices. In all cases the induced tree has
order at most five.

If two different components each have at least two vertices, an edge from
each gives an induced pair of disjoint edges. For example replacing d by
two adjacent copies with the same Y-neighborhood gives such a pair. The
same tree count still applies because the copies are true twins, and
at most one can occur in an induced tree of order at least three.

## One extra attachment suffices at an interior branch

When a branch has a common representative, its two neighbors on the
quotient path need only have distinct attachments between them. For a
nonsingleton branch, this is equivalent to at least one of the two having
an attachment other than the common representative. The other center
uses the representative. This is kernel-checked as
`Graph199.clique_branch_ports` in `Graph199CliqueBranchPorts.lean`.

A bad transition can sometimes be eliminated altogether. If a quotient
spanning path ends in the clique at t and has an interior bad transition
x–r–y, delete x–r, join x to t through the clique, and traverse the suffix
in reverse from t to r. Now r is an endpoint and only needs one attachment.
Other transitions are unchanged except for reversal. The same argument
works with a clique endpoint at the start. With two clique endpoints,
this repairs up to two bad transitions.

## The attachment condition does not follow from the graph hypotheses

Modify the four-cycle example by making X a four-vertex clique subset,
with the three-vertex branch C attached as follows. The representative
c₀ sees all of X, c₁ sees only x₃, and c₂ sees only x₄. Thus x₁ and x₂
both meet C only at c₀. The attachment edges x₁c₀, x₃c₁ and x₄c₂ are
disjoint, so removing at most two vertices still leaves C joined to the
clique whenever C survives. The argument above still shows that the
graph has connectivity three, independence number five, connected
complement, an induced four-cycle, and maximum induced tree order five.

For example, the quotient has a spanning path in the following order.

```text
x₁ c₀ x₂ x₃ a y₁ d y₂ y₃ b z₁ e z₂ z₃ x₄
```

That order cannot lift by replacing only c₀ with a spanning path through
C. Both external neighbors require the same attachment vertex, which
cannot serve as both endpoints of a nonsingleton path. It does have a
clique endpoint, so the rotation above remedies the conflict.

## Exact quotient characterization

Let Q be a clique such that every component C outside Q is a clique.
For each component let r(C) be a representative adjacent to every vertex
of Q with a neighbor in C. The representative quotient K is the subgraph
induced by Q and the chosen representatives. Call a spanning path in K
compatible if every interior representative r(C) of a nonsingleton C
satisfies the following condition. Among its two neighbors in the path,
at least one has a neighbor in C other than r(C). A singleton representative
has no extra condition. An endpoint representative also has no extra
condition, since its sole path neighbor is already adjacent to r(C).

**The original graph has a spanning path if and only if K has a compatible
spanning path.** This requires neither the connectivity hypothesis nor
the induced-tree bound.

For the reverse lift, leave singleton representatives in place. At an
interior nonsingleton representative, assign the extra attachment to the
neighbor that has it, and give the common representative to the other
neighbor. These distinct attachment vertices can be made the first and
last vertices of a spanning path of the clique C. At an endpoint
representative, list the vertices of C with r(C) next to its unique
neighbor in Q. If K consists of a single representative, list its clique
in any order. These replacements preserve adjacency and are disjoint.

For the forward contraction, take a spanning path in the original graph.
A visit to C is a maximal consecutive segment of this path in C. Distinct
visits to outside components have at least one intervening Q vertex.
For each nonsingleton C keep one visit containing a vertex other than
r(C), and for each singleton C keep its unique visit. Keep all vertices
in Q. Erase other visits and contract each kept visit to its representative.

A kept visit at either end of the original path has only one neighbor in
Q, if any, and needs no extra condition. A kept interior visit has two
distinct neighboring vertices in Q. If the visit has at least two
vertices, its two endpoint attachments in C are distinct, so one is not
r(C). If it has exactly one vertex, that vertex differs from r(C) by the
choice of visit for a nonsingleton C. Then both neighboring Q vertices
have an extra attachment. In every case the edges incident to a kept
visit become valid quotient edges by the common-representative property.

If erasing visits makes a new pair of vertices consecutive, both
belong to Q, so their edge is available. A kept visit that was interior
retains its two Q neighbors because all of Q is kept. The resulting path
uses every quotient vertex exactly once and is compatible. Multiple
visits in the original path therefore do not invalidate the equivalence.

In the 17-vertex example, the original graph admits the following spanning
path with two visits to C.

```text
x₁ c₀ x₂ a y₁ d y₂ y₃ b z₁ e z₂ z₃ x₃ c₁ c₂ x₄
```

Keep the visit c₁–c₂, erase the visit c₀ between x₁ and x₂, and contract
c₁–c₂ to c₀. The erased visit is replaced by the edge x₁x₂, and the retained
representative has two neighbors with extra attachments. Thus the example
illustrates both failure of lifting a particular incompatible order and
success of the compatible characterization.
