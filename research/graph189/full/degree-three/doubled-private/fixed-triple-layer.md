# A spanning path for the doubled-private triangle with a fixed triple layer

**Theorem.** In the doubled-private triangle under the Graph 189 hypotheses, let $h≥1$ be the number of triple-visible remotes. If $k≥15h+29$, the graph has a spanning path. If deleting at most one vertex disconnects the induced nontriple remote graph, $k≥7h+15$ suffices.

## Setup and preliminary bounds

The graph has order $n>3k$, second-smallest degree $k$, and at most $k$ positive even-distance partners per vertex. The degree-three root $z$ has eccentricity three. Its three anchors form a triangle. The middle layer consists of $k-4$ common middles $W$, each adjacent to all anchors, and private middles $P,Q,B,C$. The twins $P,Q$ have anchor $A$, and the other two have distinct anchors. The remote layer $D$ has size $c≥2k-3$. An anchor sees a remote if they have a common neighbor. Let $T$ consist of the remotes seen by all three anchors and let $F=G[D∖T]$, with $|T|=h$. Each nontriple has a supporting private, has no common-middle neighbor, and touches at most three privates. Each nonroot vertex has degree at least $k$.

For a private $J$, let $R_J=N(J)∩D$, $H_J=N_{G[D]}[R_J]$, and $a_J=|N(J)∩W|$. A solo has just one middle neighbor. The full visible sets of the three anchors have respective sizes at most $k-2,k-3,k-3$, since the foreign privates occupy distance-two places. Each singleton private has at least three solos: the remotes outside the other two visibility sets number at least $c-(k-2)-(k-3)+h≥2+h$. Write $U$ for the single-anchor remotes. Summing the three visible-set sizes gives $2c-|U|+h≤3k-8$, hence $|U|≥k+2+h$. For any private $J$, its boundary $H_J∖R_J$ has size at most $a_J+1$ after counting the root, both foreign anchors and the $k-4-a_J$ missed common middles at distance two.

No common middle meets all four privates, since it would see the root and every member of $U$ at distance two. A common middle meeting both $B,C$ and missing a twin would see every remote outside the twin anchor's visibility set (at least $k-1$), the missed twin and the root. A common middle meeting both twins and just one singleton would see all remotes outside the other singleton anchor's visibility set (at least $k$) and the root. These contradictions prove that each common middle meets at most two privates and never both $B,C$.

Suppose the set $E$ of $P$-solos has at most two members. Each single-anchor remote belongs to the boundary of one of $Q,B,C$. Indeed a single-anchor remote at the twin anchor has a closed remote neighborhood of size at least $k-1$, hence a neighbor outside its visibility set supported by $B$ or $C$. A remote visible only at a singleton anchor has a closed remote neighborhood of size at least $k$, so has at least three neighbors outside its own anchor's visibility set. One lies outside $E$ and is nontriple, hence is supported by a different member of $Q,B,C$. Furthermore a common middle meeting $Q,B$ would miss $P,C$. Every remote outside both the visible set of the anchor of $C$ and $E$ is adjacent to $Q$ or $B$; all are nontriple, and together with the root and the two missed privates they give at least $c-(k-3)-2+3>k$ distance-two vertices. The same reasoning excludes $Q,C$. Thus each common middle meets at most one of $Q,B,C$, so their three boundaries together have size at most $|W|+3=k-1$. This contradicts the lower bound on $|U|$. Both twins therefore have at least three solos by symmetry. This argument also permits common middles with no private neighbors.

The three solos of the opposite twin imply $|R_P|,|R_Q|≤k-5$, while the singleton supports have size at most $k-3$. At $J$, the root, both foreign anchors and $k-4-a_J$ missed common middles are at distance two. The remote boundary $H_J∖R_J$ therefore has size at most $a_J+1$. A solo has closed remote neighborhood of size at least $k$ in $H_J$; consequently the twins have $a_J≥4$ and the singletons $a_J≥2$.

Each single-anchor remote has at most two private neighbors, hence closed remote neighborhood of size at least $k-1$, exceeding the size of its own visibility set. A neighbor outside this set is nontriple and supported by a foreign private. Thus each member of $U$ is in at least one private boundary. Summing gives $|U|≤Σ_J(a_J+1)≤2k-4$. The sum of the three visibility-set sizes is $2c-|U|+h≤3k-8$, so
\[
  2c≤5k-12-h.
\]
Also each member of $W$ misses at most $h$ peers in $W$, by its degree and the upper bounds of three anchors, two privates and $h$ remote neighbors outside $W$.

## When (F) is 2-connected

Write $d=δ(F)≥k-3-h$. For an independent $I⊆V(F)$ of size $b>|F|-2d$, every pair in $I$ shares an $F$-neighbor because their neighborhoods lie in $F∖I$. For $x∈I∩R_J$, the other $b-1$ members, the $a_J$ common neighbors of $J$, and its anchor are all at distance two from $x$. Thus $a_J≤k-b$ whenever $I$ meets $R_J$. The closed full remote neighborhood of $x$ has at least $k-2$ members, all in $H_J$, and contains no other member of $I$. Since $|H_J|≤k-2+a_J$, we get $|I∩R_J|≤a_J+1$. The four private supports cover $I$, giving $5b≤4k+4$. Using the order bound in the complementary case gives
\[
 α(F)≤\max\{(k+h)/2,(4k+4)/5\}.
\]

Call a triple high if it has at least $2h+2$ common-middle neighbors, and let $q$ count these triples. Add the other triples to $F$ to form $F'$. Each added vertex has at least $k-3h-4$ neighbors in $F$, by subtracting at most $2h+1$ common middles, four privates and $h-1$ triples. Each has at least two such neighbors, so $F'$ is 2-connected. In $F'$, old vertices have degree at least $k-3-q$, and added ones have degree at least $k-2h-5-q$. We have
\[
 |F'|≤(5k-12-h)/2-q,\qquad α(F')≤α(F)+h-q.
\]
The lower bound $k-2h-5-q$ on the minimum degree dominates $(|F'|+2)/3$ for $k≥11h+22+4q$. It dominates the two terms in the independence bound for $k≥7h+10$ and $k≥15h+29$, respectively. Nash-Williams therefore supplies a Hamilton cycle of $F'$.

Reserve distinct common neighbors of $B,P$ as endpoints. Greedily reserve a disjoint pair of common neighbors for each high triple, avoiding the endpoints; the $2h+2$ threshold leaves at least two choices at each step. Make each pair and its triple an oriented three-vertex block, with every unassigned member of $W$ a singleton block. Two distinct blocks are compatible if the tail of either is adjacent to the head of the other, in both directions. Heads are distinct and tails are distinct, so at most $2h$ other blocks fail this test at any block. For $m=k-4-q$ blocks we have $2(m-1-2h)≥m+1$; Ore's Hamilton-connectedness criterion supplies a spanning path between the two reserved singletons. Concatenate
\[
 C, A_C, z, A_B, B,\quad\text{block path},\quad P,A,Q,\quad\text{remote path}.
\]
The remote path starts at any $Q$-solo by cutting an incident edge of the $F'$-cycle.

## When (F) is disconnected or has a cut vertex

Take $S=∅$ if $F$ is disconnected and otherwise take a singleton cut set. Write $s=|S|$. Every component of $F-S$ has order at least $k-h-2-s$, by its minimum degree. Three such components would exceed $|F|-s≤(5k-12-3h)/2-s$ for $k>3h+6$. There are thus exactly two, called $X,Y$. If one were supported by only one private, every vertex there would be a solo and its order would be at least $k-h-s$; its supporting anchor sees at most $k-2-h$ nontriples. Each component therefore has at least two available private types. Pick distinct types $J_x,J_y$ in the two components and respective attached vertices $x,y$. In each component reserve its attachment and an arbitrary different vertex as the endpoints of its eventual spanning path.

For this case call a triple high at $2h+4$ common-middle neighbors. Each other triple has at least $k-3h-7$ neighbors in $X∪Y$: outside this union it sees at most four privates, $2h+3$ common middles, $h-1$ other triples and $s≤1$ separator vertices. Any separator vertex has at least $k-3-h$ neighbors in the union. Assign each low triple and the separator vertex, when present, to a component in which it has at least half the stated count. For $k≥7h+15$, each has at least $2h+4$ candidate neighbors there. Reserve a pair per assigned vertex, avoiding the two path endpoints and all earlier pairs. At most $h+1$ vertices are assigned in total, so at most $2h+2$ candidates are forbidden at any step.

Each component has minimum degree at least $k-h-4$ and order $m≤c-k+2≤(3k-8-h)/2$, subtracting the other component, $T$, and $S$. Form an auxiliary graph on its vertices, the assigned vertices joined only to their reserved pairs, and a marker joined only to the two path endpoints. Its order is at most $m+h+2$. The sum of the degrees of any two originally nonadjacent component vertices is at least $2(k-h-4)≥m+h+2$ for $k≥5h+12$. By Bondy–Chvátal closure, one may complete the base component to a clique without changing Hamiltonicity of the auxiliary graph. In this clique arrange the disjoint reserved pairs as consecutive blocks of a spanning path between the marked endpoints; subdivide each pair by its assigned vertex and close the path through the marker. Reversing closure gives an auxiliary Hamilton cycle; deleting its marker gives the required original component path, including every assigned vertex.

Let $J_o,J_m$ be the other two privates. Choose $J_m$ to be a remaining twin whenever possible and $J_o$ with anchor different from that of $J_x$. Both requirements can be met: if $J_x$ is a twin, its remaining twin, if available, becomes $J_m$; if $J_x$ is a singleton, either remaining private has a different anchor. Reserve one common neighbor each for $J_o,J_y$ and two for $J_m$, all distinct. When $J_m$ is a twin, its at least four choices and each other private's at least two give Hall's condition. When both attachment privates are twins, $J_y$ has at least four choices and the neighborhoods of $J_o,J_m=B,C$ in either order are disjoint, each of size at least two. Hall's condition again holds.

Greedily reserve disjoint pairs of common neighbors of the high triples after those four reservations, using their $2h+4$ threshold. Build blocks for the high triples, an additional block through $J_m$ between its reserved pair, and singletons for unused common middles. There are $m'=k-5-q$ blocks where $q≤h$ is the number of high triples. The same two-way compatibility test misses at most $2h$ blocks per vertex. As $m'≥4h+3$, obtain a spanning block path between the reserved singletons for $J_o,J_y$. Starting from the free endpoint of the augmented $X$-path, traverse it to $x$, then use
\[
 x,J_x,A_1,z,A_2,A_3,J_o,\quad\text{block path},\quad J_y,y,
\]
and traverse the augmented $Y$-path from $y$ to its other endpoint. Here $A_1$ belongs to $J_x$, $A_3$ to $J_o$, and $A_2$ is the remaining anchor. This spans the original graph.

Both arguments allow $h=1$, empty low or high classes, and an empty separator in the disconnected case. The general bound specializes to $k≥44$ for $h=1$; the separate singleton-triple argument gives a sharper result in that case.

## Classical references

- C. St J. A. Nash-Williams, *Edge-disjoint Hamiltonian circuits in graphs with vertices of large valency*, Studies in Pure Mathematics (1971), 157–183. The criterion for a 2-connected graph is (δ≥\max\{α,(n+2)/3\}). [Statement in D. J. A. Welsh, p. 836](https://doi.org/10.1112/S0024609303002315).
- O. Ore's Hamilton-connectedness criterion uses degree sum at least (n+1) for every nonadjacent pair. [Statement in *On hamiltonian-connected graphs*](https://doi.org/10.1002/jgt.3190180808).
- J. A. Bondy and V. Chvátal, *A method in graph theory*, Discrete Mathematics 15 (1976), 111–135. For Hamiltonicity, adding an edge between nonadjacent vertices with degree sum at least the order preserves the answer.
