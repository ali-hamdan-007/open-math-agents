# Graph 199 at connectivity four in the triangle-free case

A connected triangle-free graph with minimum degree at least four, maximum
degree at most five, no induced tree on seven vertices, and independence
number at least six is bipartite. The argument below reduces the nonbipartite
case to 21 finite instances. An exact Z3 search reports each instance
unsatisfiable. The finite check is solver-based. The analytic order bound
and the interpretation of the SMT constraints are given here. Any larger
induced tree would contain an induced tree on seven vertices by repeated
leaf deletion.

For the exact Graph 199 path child at connectivity four, the connectivity
bound gives minimum degree four and the induced-star bound gives maximum
degree five. The independence premise gives an independent set of size six.
The checked bipartite case in `Graph199BipartiteH2.lean` supplies the required
spanning path.

## A nonbipartite graph contains an induced five-cycle

Suppose there is no five-cycle. For distinct vertices $x,y$ with a common
neighbor $z$, the path $x,z,y$ can be extended with every vertex in
the symmetric difference of $N(x)$ and $N(y)$ as a leaf on the
appropriate endpoint. Triangle-freeness excludes edges between leaves
on the same endpoint and edges from those leaves to $z$. Any edge
between opposite leaf sets would make a five-cycle together with the
path. The tree cap therefore gives
$$
 |N(x)\triangle N(y)|\le3,
 \quad |N(x)\cap N(y)|\ge(d(x)+d(y)-3)/2.
$$
By the degree lower bound the intersection contains more than half
of each neighborhood. Thus the relation “equal or have a common
neighbor” is transitive by pigeonhole, and two vertices related by
a walk of even length belong to the same equivalence class. Starting
from either endpoint of one fixed edge, connectedness puts every
vertex in one of the two endpoint classes. An edge within either
class would make a triangle because its endpoints would have a
common neighbor. These classes are a bipartition.

In a triangle-free graph any five-cycle is induced. This argument
also appears in the earlier notes and the exact reduction PR #9001.

## Order at most seventeen

Every distance is at most three. Indeed, if a geodesic starts with a
four-edge segment $x,a,v,b,y$, the two endpoint neighborhoods are
disjoint. The sets $N(x)\setminus N(v)$ and $N(y)\setminus N(v)$
provide private leaves on this path. Triangle-freeness excludes edges
within each set or to the neighboring path vertex. An edge between the two
sets, or any other unwanted incidence with the path, would shorten the
geodesic. The sets have total size at least $4+4-5=3$, giving an induced
tree of order at least eight.

A three-edge geodesic $x,y,z,w$ allows all of
$N(x)\setminus N(z)$ as private leaves of $x$ on the four-vertex
path. Triangle-freeness excludes edges to $y$ and within the leaf set.
An edge to $w$ would shorten the geodesic. At most two such leaves
can occur, so
$$
  |N(x)\cap N(z)|\ge d(x)-2.
$$
The analogous bound holds at the opposite end.

Fix a root $v$ and let $L_i$ be the distance-$i$ layer. Write $p$
for the number of vertices in $L_2$ touching $L_3$, $q$ for the
remaining vertices in $L_2$, and $r=|L_3|$. If $x\in L_2$ touches
$L_3$, the geodesic bound forces $x$ to have at least $d(v)-2$
neighbors in $L_1$. If $w\in L_3$, a geodesic from $v$ to $w$
also gives at least $d(w)-2$ neighbors of $w$ in $L_2$.
All common neighbors counted in either application lie in the stated
layer by the distance inequalities.

If the graph is 4-regular, the $L_1$-to-$L_2$ incidence budget is
$4\cdot3=12$. The preceding bounds give $2p+q\le12$ and $r\le p$,
since each of the $p$ vertices has at most two remaining neighbors for
$L_3$. Therefore $1+4+p+q+r\le17$.

For a degree-five root, every vertex $z\in L_2$ has at least two
neighbors in $L_1$. If its unique such neighbor were $y$, the edge
$vy$, the four vertices $N(v)\setminus\{y\}$ as leaves at $v$,
and $z$ as a leaf at $y$ would induce a seven-vertex tree. This is
also the saturated case of the square matching at $vy$. Thus
$$
  3p+2q \le \sum_{y\in L_1}(d(y)-1) \le 20.
$$
When the graph is 5-regular, each vertex in $L_3$ needs at least three
$L_2$ neighbors, so $3r\le2p$. It follows that
$p+q+r\le 10+p/6\le11$, since $p\le6$, and the order is at most 17.

In a connected graph with both degrees, take a degree-five root with a
degree-four neighbor. The incidence budget drops from 20 to 19. As
$r\le p$, the inequalities imply $p+q+r\le12$, hence order at most
18. Equality requires $(p,q,r)=(5,2,5)$ or $(6,0,6)$. In both
cases $r=p$ and both sides of the $L_2$-to-$L_3$ capacity
inequality saturate. The $p$ vertices each have three $L_1$
neighbors and two $L_3$ neighbors, filling their degree capacity.
Every $L_3$ vertex has exactly two neighbors in $L_2$, so the
geodesic bound implies degree four.

In the first equality case the $L_1$-to-$L_2$ budget also saturates.
Each of the $q=2$ vertices then has only two $L_1$ neighbors, no
$L_3$ neighbor, and no neighbor among the saturated $p$ vertices.
One possible neighbor in its own group leaves it short of degree four.
In the second equality case the graph on $L_3$ is triangle-free and
2-regular on six vertices, hence a six-cycle. Delete any $w\in L_3$
from that cycle. Each of its two $L_2$ neighbors has exactly one
remaining neighbor on the resulting five-vertex path. The two $L_2$
vertices are nonadjacent because their degrees are already filled.
Thus the five-vertex path extends to an induced seven-vertex tree.
Both equality cases are impossible.

## Finite check

Choose an independent set $I$ of six vertices. Its vertices have at least
24 incidences with the remaining vertices, whose degree cap gives
$24\le5(n-6)$, hence $n\ge11$. Fix a five-cycle on labels 0 through 4.
The size of $I\cap C_5$ is 0, 1, or 2. Dihedral symmetry lets the latter
two cases use $\{0\}$ and $\{0,2\}$, respectively. The other members
of $I$ can take the first available off-cycle labels. This yields the
21 cases.

Each Boolean $e_{ij}$ denotes one possible undirected edge. The static
constraints fix the induced five-cycle and the independent set, bound
each degree between four and five, and exclude triangles. For each
induced path of two, three, or four vertices in the complement of $I$,
the number of vertices of $I$ adjacent to exactly one path vertex is
at most six minus the path order. These vertices could otherwise all
join the path as independent leaves. The optional symmetry constraints
keep a lexicographically least representative under relabelings of the
off-cycle vertices within each $I$-membership class. For any two
successive vertices within such a class, their transposition changes the
edge list first at the least other index where their adjacencies
differ. Sorting these pairwise row comparisons therefore preserves a
lexicographically least representative.

For every satisfying assignment, the script finds induced seven-vertex
trees by counting six edges and checking connectivity in each candidate
seven-set. Each added clause forbids precisely one such induced pattern.
No connectivity assumption, separator inequality, Hamiltonian constraint,
or upper bound on the order of any other induced subgraph is imposed in
the solver. Every one of the 21 instances returns UNSAT. The verifier
checks each recorded tree clause by a separate component-merging
algorithm and replays each resulting SMT instance in one Z3 query.

To reproduce one case in a directory containing the scripts, run
`python finite_k4.py 17 2`. Use `--no-symmetry` to omit lex constraints.
The script requires Python 3 and `libz3.so.4`. To verify a recorded
instance, run `python audit_finite_k4.py k4-17-2.smt2`.
