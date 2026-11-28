# From exterior contacts to order and degree inequalities

Fix a longest path P of a finite simple graph G, and assume its support has no repeated vertex. The longest-path hypothesis used in the Lean statements compares P to every path in the graph, with arbitrary starting and ending vertices.

## Exterior routes

A path of r vertices outside P between ports incident with marked positions i<j implies i+1+r≤j. At an outer mark the prefix or suffix must also be at least as long as any available exterior route. Graph189ContactIntervals proves these comparisons by splicing disjoint walks. Graph189MatchedOrder sums them. If J distinct marks have routes on N vertices between successive ports, and the two outer ports have one-ended routes on N+A vertices, every exterior population W gives

    |V(G)| ≥ |W| + J + (J+1)N + 2A.

The routes may overlap each other since each comparison uses the original path separately. Graph189ExteriorMatching specializes to a genuine induced Hamilton-connected set K and an unordered matching of J marked positions to distinct members of K. This gives |V(G)|≥(J+2)|K|+J. Graph189AlmostSpanningGaps supplies the corresponding variable-length sum when one interval loses one vertex. Graph189OneExceptionalPair accounts for a single exceptional unordered pair of ports.

## Exact distance-two witnesses

For adjacent omitted vertices a,b, let A,B be their sets of contact positions on P. Every contact has a predecessor and successor. Contacts of a cannot be consecutive. Distinct contacts of a and b must be at least three positions apart. Graph189ExteriorSpacing derives these facts from the same splicing theorem. In Graph189ContactColumns, the predecessor of each contact in A, the successor of each shared contact in A∩B, and each contact in B minus A give disjoint position sets. All the corresponding vertices have ambient distance exactly two from a. Their total number is |A|+|B|. The equality between the number of contact positions and the number of actual neighbors on the path is proved in Graph189ExteriorDegree.

Write q(a) for the number of neighbors of a off P, and c for the number of common neighbors of a,b off P. When a sees at most k vertices at distance two, the off-path neighbors of b other than a and those common neighbors give an additional set of witnesses disjoint from the path witnesses. The resulting inequalities are

    |A| + degree(b) ≤ k+1+c ≤ k+q(a),
    degree(a) + degree(b) ≤ k+2q(a).

In particular q(a)≥degree(a)/2 whenever b has degree at least k. If a also has degree at least k and every ambient degree is at least three, any off-path neighbor of a implies q(a)≥2. With at most one low vertex, one of these neighbors consequently has degree at least k. A single-vertex shift bound rules out the high isolated case by giving one more distance-two witness than the number of contacts. Graph189ExteriorHalf combines the two arguments.

## Connectivity at an entire component

Let K be an entire exterior component and s the connectivity threshold. When K and P each have at least s vertices, every matching maximum across their boundary has size at least s. For a subset T of path vertices consider the union consisting of the path vertices outside T and the K-neighbors of T. If it has size below s, deleting it leaves T disconnected from the surviving vertices of K. It follows that the neighborhood of every T in K has deficiency at most |P|−s. Adding |P|−s dummy assignment choices meets Hall’s condition everywhere. Removing the dummy assignments leaves a genuine matching of at least s edges. Graph189HallDeficiency and Graph189BoundaryMatching implement this argument.

The individual .olean files and replay logs identify which declarations have passed the kernel. The geometric and metric statements above cover steps in the exterior reduction. The existence of an appropriate Hamilton-connected core or an exceptional-pair configuration in all remaining block cases requires additional formalization.

## Replay

Run MATHLIB_PROJECT=/absolute/path/to/the/pinned/project ./portable-replay.sh --full. The module list is full-modules.txt. It includes the two bundled non-mathlib inputs, Graph189TraceClosurePublic and Graph189SingleExteriorShift, under upstream. Mathlib’s published finite Hall theorem is used at the recorded revision. The buffered-boundary theorem also permits a fixed exceptional barrier F, with the contact threshold reduced by |F|. Graph189LeafBlockOrder derives the order estimate after dropping one forbidden terminal. full-import.log is the successful Lean 4.33.1 import and axiom audit of the public conclusions.
