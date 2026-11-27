# Degree-three diameter-three order computation

This is an exhaustive finite solver computation for each explicitly reported k. The solver was not configured to emit proof certificates. It does not constitute a general theorem for untested k, or for eccentricity three at a degree-three vertex without a global diameter assumption.

Root vertex 0 has degree three and neighbors 1,2,3. All other vertices have degree at least k, and at least one has degree exactly k. We require global diameter at most 3 and at most k vertices at distance two from any vertex. In this diameter range those are exactly the positive even-distance partners. Put B=N₂(0), C=N₃(0); k−3≤|B|≤k follows from the three anchor degrees and root cap. The minimum |B| considered is one because n>3k>4 and the graph is connected.

The anchor-induced graph has one of four isomorphism types 0,1,3,7, the masks indexing the three possible edges in lexicographic order. Give every B vertex its nonzero 3-bit mask of adjacent anchors. Canonically sort the list of masks and minimize it over automorphisms of the anchor graph. Discard profiles where an anchor fails its degree bound. For anchor i, every other nonadjacent anchor is distance two via the root, as is every missed B vertex that is adjacent to a neighbor of i in the anchor graph. Subtract these forced non-C partners from k to obtain three integral capacities. Each C vertex has a B neighbor with some mask in the profile, so its visibility to the anchors consumes at least that mask. A three-coordinate packing recurrence subtracts one available mask at a time until no coordinate-wise feasible subtraction remains, maximizing the count of packed masks. This maximum bounds |C| above. The program checks every total order from 3k+1 to 4+|B|+this maximum.

For each order and profile, seek.py fixes the root, anchor and B-to-anchor edges, forbids C-to-anchor edges and requires a B neighbor for each C. It uses an unordered Boolean edge variable per pair and asserts the exact definition of a distance-two pair as a nonedge admitting a common neighbor. Every pair is constrained to be adjacent, distance two, or adjacent to a distance-two vertex of the other. The degree and distance-two caps are cardinality constraints. Unlabeled C vertices and B vertices with identical masks are interchangeable. Lexicographic row-major minimization of the adjacency matrix implies the encoded ordering of the two neighbor rows (with their own two columns suppressed) for any allowed transposition. Using those comparisons preserves at least one representative of every graph.

Run in this directory with Python 3 and system libz3.so.4. The optional last argument is the per-instance timeout in seconds. To obtain the original k=4 witness and k=5 counts without symmetry breaking, replace 'from seek import search' in a copy of exhaust.py with 'from original import search'. The symmetry version tests the same orders and profiles, but may produce a different labeled witness. If any query times out it prints unknown, which contributes no unsatisfiability claim.

    python exhaust.py 4 30
    python exhaust.py 5 30
    python exhaust.py 6 30
    python exhaust.py 7 30
    python exhaust.py 8 30
    python exhaust.py 9 30

| k | Canonical degree-feasible profiles (including those eliminated by order bound) | Orders checked | Queries per order | Outcome |
|---|---:|---|---|---|
| 4 | 183 | 13–14 | 30,8 | one satisfiable profile at 13, all other queries unsatisfiable |
| 5 | 224 | 16–18 | 32,11,2 | all unsatisfiable |
| 6 | 244 | 19–22 | 34,13,5,2 | all unsatisfiable |
| 7 | 252 | 22–26 | 34,15,7,5,2 | all unsatisfiable |
| 8 | 254 | 25–30 | 34,15,9,7,5,2 | all unsatisfiable |
| 9 | 255 | 28–34 | 34,15,9,9,7,5,2 | all unsatisfiable |

The fourteen-vertex queries at k=4 also incorporate all profiles of that order, regardless of covering pair. The witness in all4.log has degree sequence in vertex order (3,4,4,4,4,4,5,4,4,5,4,5,4), eccentricity three at every vertex, and every vertex has exactly four distance-two partners, as checked by breadth-first search. It has the Hamilton path 0,1,2,4,10,9,8,7,3,6,11,12,5. Thus the order cutoff n≤3k cannot hold for all k, even though no example above 3k exists here for k=5 through 9.
