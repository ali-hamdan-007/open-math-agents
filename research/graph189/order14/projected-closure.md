# A projected degree certificate for the adjacent one-miss shape

Let a simple graph on 14 vertices have layers `{z}, {a,b}, W, R` of sizes 1, 2, 5, 6 by distance from `z`. Assume every vertex except `z` has degree at least five and every vertex has at most five vertices at distance exactly two. Suppose `a,b` are adjacent, and each misses precisely one member of `W`, with distinct misses `x,y`. The graph has complete degree-sum-13 closure and hence a spanning path.

## Four forced remote neighborhoods

An anchor sees its missed middle vertex at distance two through the other anchor. A remote vertex with a neighbor in W other than the missed vertex is also at distance two from that anchor. Since at most four of the six remotes can be of this kind, at least two have the singleton middle neighborhood consisting of its missed vertex. Doing this at both anchors gives four distinct remotes. Order W as x, y, and the three other vertices. Order R so its six nonempty W-neighborhood masks are `(1,1,2,2,s,t)`, with `1 ≤ s ≤ t ≤ 31`.

## The finite degree calculation

Only the two additional remote masks and the ten possible edges inside W enter. For each middle vertex w, let N be its neighbors in W and Q its neighbors in R. Its degree is exactly the number of its adjacent anchors plus |N| + |Q|. The following disjoint sets count toward its distance-two bound.

* The vertex z, and also its missed anchor when w is private.
* Every vertex in W other than w and its neighbors that shares an anchor or remote with w.
* Every remote outside Q that touches a vertex in N, or that has fewer than |Q| neighbors in W.

For the last condition, if r lies outside Q and has k neighbors in W, it has at least 5 − k neighbors in R. Of its five possible remote neighbors only 5 − |Q| are outside Q. Thus k < |Q| forces a two-edge path through Q.

For each of the 496 mask pairs and 1,024 middle graphs, reject choices giving any middle degree less than five or any preceding lower bound above five. The surviving projections are distributed as follows.

| Number of middle vertices of degree at least eight | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| Number of surviving projections | 0 | 0 | 0 | 13 | 21 | 6 |

These counts concern labeled middle graphs and the two sorted masks, without specifying any edge inside R. They are counts of projections satisfying necessary inequalities. All actual graphs in this shape project to one of these cases.

Run `python3 verify_189_projected_closure.py` with Python 3.10 or later. Expected output:

```
496 remote-mask pairs x 1024 middle graphs
high middle vertices: [(3, 13), (4, 21), (5, 6)]
```

## Closure lemma

Let G be a graph on fourteen vertices, with a distinguished z of degree at least two and all vertices of C = V minus {z} of degree at least five. Assume T is a three-element subset of W contained in C, each of whose members has degree at least eight. Suppose U is a four-element subset of C disjoint from W, with each member having exactly one neighbor in W, belonging to {x,y} within W. For each of x,y suppose there is an anchor in C outside W and U of degree at least six, adjacent in G to neither that private vertex nor any member of U. Then every degree-sum-13-saturated supergraph H of G on the same vertices is complete.

Indeed, every H-vertex of degree at least eight sees every other vertex of C because all members of C have degree at least five. Thus T is universal to C. Each u in U had at most one G-neighbor in T, gains at least two neighbors, and has H-degree at least seven. If T misses both x and y, each u gains all three and reaches degree eight. Otherwise take a private member of T. Its corresponding anchor gains an edge to that member, reaching H-degree at least seven. Each u, also of H-degree at least seven, must be adjacent in H to that anchor. This further new neighbor lies outside T, so every u again has H-degree at least eight.

All seven vertices of T union U are now universal to C. Every remaining member of C therefore has degree at least seven, so saturation forces all remaining pairs of C to be edges. Each member of the resulting 13-clique has degree at least twelve. With degree at least two at z, saturation forces all remaining edges at z.

For the layered graph above take its four singleton remotes for U. Each anchor has degree six, coming from z, the other anchor, and four middle neighbors. Apply the lemma to the iterated degree-sum-13 closure. The standard path-closure theorem on fourteen vertices preserves traceability at each addition, so the complete closure gives a spanning path in G.
