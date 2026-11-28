# Compact moderate-degree coverage at degree four

Put $p=|P|$ for a longest path in the deletion of a minimum-degree vertex $z$. Write $b$ for the number of retained vertices omitted by $P$. The established moderate order and deletion-gap bounds give $p\ge7$, $b\ge3$ and $p+b+1\le14$. These inequalities leave ten order pairs and $b\le6$.

## Requirements on a genuine layout

The graph part is independent of degree and order.

- `Graph189ContactLayout.Layout` fixes labelled path and exterior embeddings, exhaustive together with $z$. It retains all exact exterior edges and all exterior-to-path contacts.
- `layout_of_original_walk` derives the layout from a walk in the deletion and a certified family of representatives. The mask relabeling leaves the indexing of $P$ fixed.
- `Layout.tail_spacing` and `Layout.contact_spacing` accept any explicit exterior path. If its order is $q$, a contact of its endpoint is at least $q$ positions from either end of $P$. Two distinct contacts of the two endpoints must have at least $q$ positions strictly between them. These follow by replacing a path tail or interval. The instance $q=1$ excludes consecutive contacts of a single exterior vertex.
- `Layout.degree_floor` gives $|A(x)|+d_E(x)+1\ge k$. Equality forces an original edge to $z$.
- `Layout.contactOnClosed` forces a contact in every nonempty edge-closed exterior set from connectivity of the deletion.
- `Layout.evenCap` charges only genuine original distance-two witnesses. A path noncontact can arise from an immediate path neighbor of a contact or from a contact at an exterior neighbor. A nonadjacent exterior peer can arise from a shared path contact, a shared exterior neighbor or two forced edges at $z$.
- `Layout.prefixEven` retains the same budget after setting unassigned rows to zero and restricting exterior peers to assigned rows. Every partial witness is still a genuine full witness.

The independent replay uses these conditions alone and obtains exactly the 30 existing canonical catalogue rows. It does not require a theorem limiting how many exterior vertices are isolated or a separate cross-contact cardinality inequality.

## Finite verification

1. Use the checked incremental graph masks through order five and the order-six extension in `Graph189ExteriorRepresentatives6.lean`. The six-vertex stage checks 1,088 labelled extensions in 17 batches. Each witness supplies a permutation into a selected representative. The color-refinement algorithm can choose candidates without becoming a proof dependency.
2. For each labelled exterior representative, record one explicit simple exterior path for every nonzero rooted or endpoint-to-endpoint span used by the search. Verify all vertices, consecutive edges, distinctness and endpoints. The certificate uses the length of an exhibited path as a lower bound, so it needs no optimality certificate.
3. At each root enumerate all subsets of the interval allowed by its checked rooted span. Check the deletion degree floor and nonconsecutiveness. Enumerating subsets of the interval avoids iterating over all $2^p$ masks. A genuine row lies in this list by interval containment.
4. Assign vertices in increasing order of the local-choice count. Whenever a row is assigned, check its pair spacing against assigned peers and the partial even budgets. These checks are necessary for every prefix of a genuine layout. The order is a permutation of exterior labels, so a proof by induction on the assignment order establishes full coverage.
5. On a full row, check the contact condition for the listed exterior components. Validate each component list as a nonempty edge-closed set. A separate connectedness proof for a listed set is unnecessary, since closure alone implies the contact requirement.
6. Compare the resulting canonical keys with the existing terminal catalogue. Split computation into fixed $(p,b,m)$ blocks or validation of a precomputed prefix tree. Validate the tree's complete child list at each visited prefix, since trusting only a list of surviving keys would miss the coverage requirement.

| $p$ | $b$ | Local Cartesian tuples | Prefixes passing spacing and partial parity | Full rows before contact connectivity | Canonical keys |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 7 | 3 | 3 | 5 | 1 | 1 |
| 7 | 4 | 4 | 5 | 0 | 0 |
| 7 | 5 | 5 | 7 | 0 | 0 |
| 7 | 6 | 7 | 13 | 0 | 0 |
| 8 | 3 | 108 | 12 | 2 | 2 |
| 8 | 4 | 514 | 23 | 1 | 0 |
| 8 | 5 | 2,128 | 29 | 0 | 0 |
| 9 | 3 | 1,946 | 24 | 3 | 3 |
| 9 | 4 | 23,841 | 85 | 21 | 20 |
| 10 | 3 | 21,048 | 40 | 4 | 4 |
| **Total** | | **49,604** | **243** | **32** | **30** |

Reproduce from this directory with `PYTHONDONTWRITEBYTECODE=1 python audit_k4_layout.py`. The script requires equality with the 30 keys in `../moderate-certs/patterns-4.json`. Generate the order-six extension with `PYTHONDONTWRITEBYTECODE=1 python generate_exterior_relabels.py 6 --first 6 --chunk-size 64`.

## Short-path reduction

The $p=7,8$ cases admit an independent graph argument. It leaves just the three triangle keys. In particular the only cases needing finite enumeration are $(p,b)=(9,3),(9,4),(10,3)$, all covered by the checked representations through five vertices.

Every exterior component contains a contacting vertex $x$. Since $p\le8$, tail spacing forbids a rooted exterior path of order four from any contacting vertex. A rooted path of order three restricts its contacts to the central positions, of which there are at most two, and these are consecutive. Such a vertex has at most one contact.

Suppose $x,y,w$ form a rooted exterior path. Then all exterior neighbors of $w$ lie in $\{x,y\}$. If an exterior neighbor $v$ of $x$ lies outside $\{y,w\}$, the reversed path $w,y,x,v$ forbids all contacts of $w$. Its exterior degree is at most two, contradicting deletion degree at least three. Thus all exterior neighbors of $x$ lie in $\{y,w\}$. If $xw$ were absent, $x$ would have exterior degree one and need two contacts. Consequently $x,y,w$ form a triangle. An additional neighbor of $y$ or $w$ would extend one of the two orders of the triangle starting at $x$ to a rooted path of order four. Hence the triangle is the entire component.

If no rooted exterior path of order three starts at $x$, every exterior neighbor of $x$ has exterior degree one. If there are at least two such neighbors, each has a rooted path of order three through $x$ to another neighbor. It then has at most one contact but needs two. Thus this component is a singleton or an edge.

Every vertex in these three component types has deletion degree exactly three.

- A singleton has exactly three contacts. There are at most six interior positions, and no two contacts are consecutive. The three predecessors and the successor of the last contact are four distinct path nonneighbors at distance two.
- An edge requires at least two contacts at either endpoint. For $p=7$ the allowable interval is $\{2,3,4\}$ in zero-based coordinates. Each row would have to be $\{2,4\}$, violating the spacing of distinct contacts at the endpoints of an exterior edge. For $p=8$ the interval is $\{2,3,4,5\}$. A contact at 3 or 4 would force every contact at the opposite endpoint to equal it, since no other site in the interval lies three positions away. Both rows therefore equal $\{2,5\}$, with four distinct path nonneighbors at distance two.
- A triangle requires one contact per vertex. Every vertex has a rooted path of order three and therefore has exactly one contact. The endpoints of every edge in the triangle also have a three-vertex route through its third vertex. That route forces the contacts of the two endpoints to coincide. Each triangle root has the immediate path predecessor and successor of this common contact as distance-two witnesses.

All exterior vertices now meet $z$ by the exact deletion-degree bound. A singleton or edge cannot coexist with any other component, since a root already has four path witnesses and sees every vertex of the other component at distance two through $z$. Two triangles cannot coexist, since a root in one triangle sees two path witnesses and three vertices of the other triangle. With $b\ge3$ the exterior is therefore a single triangle. Its common contact is index 3 when $p=7$ and index 3 or 4 when $p=8$.
