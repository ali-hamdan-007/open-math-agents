# Written on the Wall II 133, the radius-four case

**Claim.** Let G be a finite connected graph of radius four with no
four-cycle (even with chords) and no induced eight-vertex path. Then
the average independence number of an open neighborhood is at most
three. This proves the mathematical statement of
`WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H2`
from merged Open Math Agents PR #7401. The reduction’s additional
density and large-neighborhood hypotheses are unnecessary.

The proof combines structural arguments with a small exact C++
enumeration. The verifier, `check_radius4.cpp`, is adjacent to this
note. There is no claim of a Lean proof.

## An induced anchor from the radius

Fajtlowicz’s induced-ciliate theorem says that a graph of radius r
contains an induced r-ciliate. Such a graph consists of an even
cycle of order 2t with a path of length r−t attached at each cycle
vertex. The t=1 case is the path of order 2r. See Theorem 4 of
DeLaViña, Larson, Pepper and Waller, which cites Fajtlowicz.

For r=4 the t=1 case is an induced P8 and t=2 contains a four-cycle.
The only anchors left are the eight-cycle and the six-cycle with one
pendant leaf at each vertex.

## The eight-cycle anchor

Let C be an induced eight-cycle. Call an outside vertex a boundary
vertex if it has a neighbor in C. Enumerate its nonempty
neighborhood in C by testing all 255 masks against both forbidden
subgraphs. Exactly 32 masks survive. Each has at least two
neighbors, and for each there is an induced path on four vertices
starting at the boundary vertex with the other three vertices in C.
Two distinct boundary vertices cannot have the same mask, since
two common neighbors would yield a four-cycle. In particular, the
boundary is finite with one vertex of each mask.

The verifier enumerates all possible graphs induced by C together
with the entire boundary. It adds the vertices in contact-mask
order and tests every subset of possible edges to earlier boundary
vertices. An edge is possible only when the graph on C and those
two boundary vertices admits it. It tests square-freeness and
induced-P8-freeness after each addition. There are 790 labeled
boundary graphs under this ordering convention, including bare C.

Every vertex of G is at distance at most four from C. Indeed, for
a shortest path of length at least five from an outside vertex to
C, its penultimate vertex x is in the boundary. The first four
edges of the path starting at x and going away from C, together
with the four-vertex induced path from x into C, form an induced
P8. Vertices beyond x on the shortest path have no neighbor in C.
Consequently every vertex is within distance three of C and its
full boundary taken together.

For a proper extension of C, connectedness ensures a nonempty
boundary. Start the following recursion for each corresponding
boundary graph. At every state the current graph is a proposed
induced subgraph of G with all boundary vertices included. It is
connected. Pick any current vertex u at distance at most three
from every current vertex, measuring distances within the state.
The replay checks that a vertex u with this property always
exists whenever the branch has not already been rejected.

If G had radius at least four, it would contain a vertex z at
distance at least four from u. Such a z must be outside the
current state. A shortest path from z to the current vertex set
has length s in {1,2,3}, because that set contains the full
boundary. Write the newly added vertices in order from the
current set to z. Only the first touches the current set, and
its contact set is a nonempty subset of the current vertices
outside C. Any of these contacts v must have current distance
at least 4−s from u, since a shorter path would also put z within
three of u in G. The newly added vertices induce a path by
shortestness.

Enumerate every allowed length and every such first contact set.
A contact set introducing a four-cycle is forbidden, as is any
extension introducing an induced P8. The only potential new
four-cycle would have the first new vertex and an existing pair
of contacts with a common neighbor. Record (u,z) as a witness
pair in each expansion. At every state, discard the branch if
any recorded pair has become distance at most three, since the
pair must also have distance at least four in the proposed G.
This recursively covers every extension to a graph G of radius
at least four.

The exact replay exhausts every branch after 819 states, the
largest on 18 vertices. This rules out every proper extension
of C in the radius-four case. Thus G=C8 in this branch and
every local independence number is two.

## The six-cycle with six leaves

Let H be a six-cycle whose six corresponding pendant leaves
are also included in the induced anchor. Let B be the vertices
outside H with a neighbor in H, and let Y be the rest. The
following finite local checks are done by the verifier. They
use graphs on at most sixteen vertices and depend only on
forbidden four-cycles and induced P8s.

- The 30 possible nonempty contact sets in H are a single cycle
  vertex, an adjacent cycle pair, a cycle vertex and its own
  leaf, or an opposite cycle pair together with zero, one or
  both of its own leaves. Call a vertex of the last type a
  bridge. There are at most three bridges in G, because two
  sharing an opposite pair would share two neighbors.
- Every edge inside B has a common neighbor in H. No two
  bridge vertices are adjacent.
- A vertex in B adjacent to Y must be a bridge. Each bridge
  starts a five-vertex induced path whose other vertices are
  in H.
- A chordless three-edge path from one bridge to a distinct
  bridge through two vertices of Y is impossible.

For any square-free graph, the subgraph of an open neighborhood
is a matching plus isolated vertices, since a two-edge path
inside a neighborhood would give a four-cycle. Hence the sum
of the local independence numbers equals twice the edge count
minus three times the triangle count. Use this weighted count
for the rest of the proof.

The anchor has 12 vertices and 12 edges and no triangles, so it
has slack 12 against three per vertex. Adding the contacts of
a singleton costs 2. An adjacent cycle pair or a cycle vertex
with its leaf costs 1, accounting for its triangle. A bridge
touching l optional leaves costs 4−l, accounting for its l
triangles. Thus all contacts add at most one excess per bridge,
at most three in total. Any edge within B costs at most −1,
because it has a triangle with a common core neighbor. These
triangles are distinct for distinct edges in B, and distinct
from the contact triangles already counted. The induced graph
on H and B still has slack at least nine.

Let T be a connected component of G[Y] and let x be a bridge
adjacent to T. Such a bridge exists by connectedness. In the
graph on T and x, an induced four-vertex path starting at x
would extend the five-vertex path into H to an induced P8.
It follows that every vertex of T is at distance one or two
from x in that subgraph. The neighbors of x induce a matching.
Each distance-two vertex has a unique neighbor in the first
layer, since two would form a four-cycle with x. Two distance-two
vertices with different parents cannot be adjacent, since that
edge would complete an induced four-vertex path starting at x.
Under a given parent the edges between its children form a
matching. Because T is connected, there are at most two
first-layer vertices, which are adjacent if there are two.
The parent edges, plus that first-layer edge if present, give
a spanning tree of T. Each extra edge is between siblings
and forms a distinct triangle with its parent. Thus the
weighted count within T is at most 2(|T|−1). For each adjacent
bridge the crossing edges have weighted count at most two,
since either there is one edge or there are two edges and their
triangle. These crossing triangles are distinct and have not
been counted inside T.

If t bridges are adjacent to T, the contribution is therefore
at most 2(|T|−1)+2t. Two of these bridges must share a neighbor
in T. Otherwise a shortest path through T between the bridges
would have exactly three edges by the distance-two bound. It
would be chordless because the bridges are nonadjacent and the
path is shortest with internal vertices in T. The finite
local check rules this out. By square-freeness a bridge pair
has at most one common neighbor. It therefore occurs in at
most one component’s list of adjacent bridges.

The excess of the contribution of T over three per vertex is at
most max(0,2t−2−|T|), which is at most binom(t,2) for t=1,2,3.
Thus the total excess for all of Y is at most three, since
there are at most three unordered bridge pairs. The slack
from H and B more than pays for this, proving the claim.

## Replay

```sh
g++ -O3 -Wall -Wextra -Werror -std=c++20 check_radius4.cpp -o check_radius4
./check_radius4
```

The square check uses the equivalent predicate that two distinct
vertices have two distinct common neighbors. The induced-path
check extends a path one vertex at a time and forbids adjacency
to any earlier vertex except the endpoint. The distance routine
is breadth-first search through distance three. The code treats a
missing current 3-center or exhaustion of its size guard as an
error. Neither occurred in the replay.

## Sources

- Siemion Fajtlowicz, “A characterization of radius-critical graphs,”
  Journal of Graph Theory 12 (1988), 529–532.
  [DOI](https://doi.org/10.1002/jgt.3190120409)
- Ermelinda DeLaViña, Craig E. Larson, Ryan Pepper and Bill Waller,
  “A Characterization of Graphs Where the Independence Number Equals
  the Radius,” Graphs and Combinatorics 28 (2012), 315–332, Theorem 4.
  [Paper](https://www.uhd.edu/documents/academics/sciences/0911-0119.pdf)
- The exact radius-four residual is H2 of the merged reduction.
  [Open Math Agents #7401](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7401)
