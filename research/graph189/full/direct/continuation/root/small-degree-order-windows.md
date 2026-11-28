# A finite route through every order at second-smallest degree at most five

The checked layer-cover estimate gives, at any vertex x, the upper bound

    n ≤ 1 + deg(x) + k + floor((k+1)²/4).

Taking a vertex whose degree is the second entry k gives n≤11, 15, 20 at k=3, 4, 5. The previously checked k≤2 reduction and the moderate-window argument therefore leave only the following additional orders. Counts are attachment patterns before testing optional edges. Distinct labeled contact patterns can represent the same graph.

| k | n | Attachment patterns | Survive |
|---:|---:|---:|---:|
| 4 | 15 | 72 | 0 |
| 5 | 18 | 88 | 0 |
| 5 | 19 | 227 | 0 |
| 5 | 20 | 876 | 0 |

This supplies a second computer-assisted route to these degrees within the full paper argument. The order and saturation lemmas passed the pinned Lean kernel. Enumeration coverage, routing and the full parent still have formal proof obligations.

## Exhaustive exterior generation

Use the longest path P of H=G−z from the moderate computation, with z a minimum-degree vertex, p the order of P and b=n−p−1. The path gap gives b≥ceil(k/2)+1. The endpoint degree sum gives p≥2k−1. These two statements apply outside the moderate window as well. Its only use in the old enumeration was to specify the upper bound on b.

Every component of the induced exterior E touches P at some vertex x. A longest exterior path starting at x can be joined to either direction of P from its mark. If that exterior path has L vertices, at least L positions on P precede the mark and at least L follow it. Consequently L≤floor((p−1)/2). Generate connected potential components with at least one such vertex, allowing all simple graphs when the size already fits. This generation is exhaustive by induction. For a feasible connected graph root a spanning tree at a witnessing x, then delete any other leaf of that tree. The remaining graph is connected and no path starting at x can have grown. Re-add the deleted vertex with every possible nonempty neighborhood and identify isomorphic graphs. Finally enumerate multisets of components of total size b, applying the earlier minimum internal degree and at-most-one-isolate tests. All later contact restrictions are those in moderate-small-completion.md.

## Forcing an actual path

Once a vertex r has k definite vertices at distance two, every other vertex reached by a walk avoiding them is adjacent to r. Along such a walk the distance from r cannot reach two for the first time. The Lean theorem Graph189SaturatedEven.forced_edge gives this conclusion in the original graph.

For example, suppose k exterior vertices touch P only at the same internal position t. The previous vertex r then sees all k at distance two. It is adjacent to the far endpoint of P, since P avoids the witnesses. Rotate there. Starting from an exterior contact, follow P from t to its last endpoint, cross to r, then traverse the remaining prefix backwards. This adds a vertex to the longest path in H. This eliminates the additional one-port pattern at n=19.

A second argument handles the six-vertex exteriors at n=20. Here k=5, hence every original degree is at least five by the rooted order bound. Suppose an exterior component of size b spans a path beginning at a contact, its only position on P is the middle t, and p=2b+1. An edge between opposite tails at distances i and j from t would give two choices for a path starting at t, with b+2+i−j and b+2+j−i vertices. Choose the longer and prepend the b exterior vertices. The new H-path has at least 2b+2 vertices. Consequently deleting t and z leaves the two tails and the exterior as three connected components of size b.

At b=6 each component has internal minimum degree at least 5−2=3. It has a spanning path starting at any prescribed vertex by Dirac's theorem, also a consequence of the fork's rooted local Ore theorem. Each component has a neighbor of each separator vertex by two-connectivity. In a component of size at least two, the two boundary vertices can be chosen distinct. Otherwise their common vertex would be a cut vertex. Route across this middle component using at least two vertices, join through t and z, and traverse the two outer components completely. The path uses at least 6+2+6+2=16 vertices, meeting n−ceil(k/2)−1. This contradicts the path gap.

## Replay

From the continuation directory run

```sh
python3 root/moderate_exterior_search.py 4 --orders 15 15 --complete
python3 root/degree_window_exteriors.py 5 18 20
c++ -std=c++17 -O2 verify/small-degree-independent.cpp -o /tmp/graph189-degree-window
/tmp/graph189-degree-window 4 15 15
/tmp/graph189-degree-window 5 18 20
```

The C++ implementation instead derives the three components from the actual upper graph for each interval and checks that they are connected in its lower graph. It applies the general saturated-shell implication to all forced distance-two witnesses. Both computations exclude every pattern at the four displayed orders.
