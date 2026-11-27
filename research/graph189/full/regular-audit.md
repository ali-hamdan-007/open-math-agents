# Independent audit of the regular case of Conjecture 189

The regular-case proof is correct at paper level. It proves a Hamiltonian cycle for every finite connected $k$-regular graph with $k\ge2$ satisfying the original even-distance bound. The connected $k=1$ case is $K_2$ and has a Hamiltonian path. There is no nontrivial connected $k=0$ case.

The published [Asratian–Granholm paper](https://liu.diva-portal.org/smash/get/diva2%3A1665796/FULLTEXT01.pdf) establishes two inputs. Theorem 1.6 gives a Hamiltonian cycle whenever a connected regular graph has at most $k$ distance-two vertices at each vertex and each induced radius-two ball is 2-connected. Lemma 2.2 gives the split-ball structure used below. The original even-distance condition implies the paper's distance-two cap. When $k\ge3$, every radius-two ball is connected, since geodesics to its center stay in the ball, and contains at least $k+1\ge4$ vertices. Thus failure of 2-connectivity supplies a cut vertex $z$ to which the lemma applies. The $k=2$ connected case is a cycle.

By Lemma 2.2, the radius-two ball centered at $z$, with $z$ removed, has just two components $X,Y$, each of size $k$. Write $A=N(z)\cap X$, $B=N(z)\cap Y$, $P=X\setminus A$, $Q=Y\setminus B$, and $T=N_3(z)$. Both $A,B$ are nonempty because any component of this ball contains a first step of a shortest path from $z$. Their sizes $a,b$ sum to $k$, so $|P|=b\ge1$ and $|Q|=a\ge1$. Each anchor in $A$ sees all $k-1$ other vertices of $X$ and $z$, exhausting its degree, and similarly for $B$. The distance-two layer from $z$ is $P\cup Q$ of size $k$. The full positive even-distance cap therefore excludes distance four from $z$, and hence distances larger than four by taking a prefix of a geodesic. Thus $X,Y,T,\{z\}$ partition the graph, with $\operatorname{ecc}(z)\le3$.

Every vertex of $P$ has a neighbor in $T$, since its side has only $k-1$ other vertices and no edge to $z$ or $Y$; the same holds for $Q$. Every $t\in T$ has a neighbor in $P\cup Q$. Let $T_P,T_Q$ be the subsets of $T$ with neighbors in $P,Q$, respectively. A vertex of $A$ sees all $b$ vertices of $B$ and all of $T_P$ at distance two, through $z$ and $P$, respectively, so $|T_P|\le a$; similarly $|T_Q|\le b$.

## Mixed remote branch

If $t\in T_P\cap T_Q$, then all $k$ anchors are at distance two from $t$, so the full even-distance cap yields $\operatorname{ecc}(t)\le3$. Every component of the induced graph $F=G[P\cup Q\cup T]$ has a remote, since each $P$- or $Q$-vertex has a remote neighbor. Any length-three-or-shorter path from $t$ to a remote stays in $F$, since entering any vertex of $A\cup B\cup\{z\}$ requires at least two edges from either endpoint. Consequently the remotes in all components are connected to $t$ within $F$, and $F$ is connected.

If $t$ were not adjacent to every other vertex of $F$, a shortest $F$-path would provide a vertex at distance two from it in $F$. Since $F$ is induced, that vertex is nonadjacent to $t$ in $G$ and has distance two there, exceeding the cap already exhausted by the anchors. Thus $t$ is universal in $F$, giving $k=\deg(t)=k+|T|-1$ and $|T|=1$. Every vertex of $P$ must then see every other vertex of $X$ and $t$ to attain degree $k$. The same holds with $Q,Y$. Hence $X,Y$ are cliques, and a cycle runs from $z$ to any anchor of $A$, through $X$ to a vertex of $P$, through $t$ to a vertex of $Q$, through $Y$ to an anchor of $B$, and back to $z$. Both types of endpoint in each clique are nonempty and distinct.

## Pure remote branch and endpoint closure

Otherwise $U=T_P$ and $V=T_Q$ partition $T$ and are both nonempty. The only possible edges from $X\cup U$ to $Y\cup V$ run from $U$ to $V$ by the split-ball structure and purity. At least one such edge exists. Otherwise these sides connect only through $z$, and a vertex $r\in U$ has all of $A$ at distance two, all of $B$ at distance four, and any $s\in V$ at distance six. The total $a+b+1=k+1$ contradicts the full even-distance cap at $r$.

Fix an edge $rs$ between $U,V$ and arbitrary anchors $a_0\in A,b_0\in B$. In $L=G[X\cup U]$, the internal degrees are $k$ on $P$, $k-1$ on $A$, and at least $k-|V|\ge a\ge |U|$ on $U$. Set $u=|U|$, so $1\le u\le a\le k-1$. Add a marker $m$ with exactly two neighbors $a_0,r$, giving order $N=k+u+1$. Each of the following edges may be added by [Bondy–Chvátal cycle closure](https://www.sciencedirect.com/science/article/pii/0012365X76900789) because the current degree sum reaches $N$.

| Edges added if absent | Degree lower bounds at the time of addition |
|---|---|
| $a_0r$ | $k$ and $u+1$ |
| $a_0$ to the other members of $U$ | $k+1$ and $u$ |
| $r$ to all of $X$ | $u+2$ and $k-1$ |
| All remaining edges between $X,U$ | $k$ and $u+1$ |
| Missing edges inside either of $X,U$ | Both degrees at least $k$, and $2k\ge N$ |

At the fourth step every $U$-vertex has gained its previously absent $a_0$-edge and every $A$-vertex has gained its previously absent $r$-edge. At the fifth step each $U$-vertex sees all $k$ members of $X$. The resulting clique on $X\cup U$ admits a spanning cycle with the marker using the two prescribed edges. Closure preserves Hamiltonicity through every addition, and no marker edge was added. Deleting the marker from a Hamiltonian cycle in the original marked graph gives a spanning path in $L$ with endpoints exactly $a_0,r$. The symmetric right-side path has endpoints $b_0,s$. These paths are disjoint, and the edges $rs,za_0,zb_0$ join them into a Hamiltonian cycle of the original graph.

The proof uses the full even-distance cap at the split center, a mixed remote if present, and a pure remote to force a cross edge. The distance-two cap alone would not justify those unrestricted-diameter steps. The argument is not a Lean proof and covers the regular subfamily of the exact conjecture, while the OMA branches also allow irregular graphs.
