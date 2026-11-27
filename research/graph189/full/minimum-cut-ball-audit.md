# Independent audit of the irregular split-ball theorem

The argument in [the split-ball proof](../split-ball/proof.md) is sound at paper level. For a finite connected simple graph of minimum degree $k\ge2$, assume each vertex has at most $k$ vertices at positive even distance. If a degree-$k$ vertex $z$ is a cut vertex of an induced radius-two ball, the graph has a Hamiltonian cycle. The relocation argument below reduces this to a ball centered at $z$. In Conjecture 189 this applies when $\delta=\sigma$ and this specific ball exists. Degrees above the minimum and the graph diameter can be arbitrary.

## Independent split-ball checks

- A component of $B_2(z)-z$ contains a neighbor $x$ of $z$, since each distance-two vertex has a predecessor in $N(z)$. All neighbors of $x$ lie in that component or are $z$, so the component size is at least $k$. The bound $|B_2(z)-z|\le2k$ therefore forces exactly two components of size $k$, and $|N_2(z)|=k$. Any eccentricity beyond three would supply a distance-four vertex along a geodesic, exceeding the cap.
- Write $X,Y$ for the two sides, $A,B$ for their anchor subsets, and $P=X\setminus A,\ Q=Y\setminus B$. Both anchor sets are nonempty and $a+b=k$. Every anchor exhausts its degree on its side and $z$. Since $P,Q$ each have at most $k-1$ possible neighbors outside the outer layer $T=N_3(z)$, each vertex of $P\cup Q$ sees $T$. Each outer vertex sees $P$ or $Q$ by a geodesic to $z$.
- In the partition $T=U\sqcup M\sqcup V$, an anchor in $A$ sees $B$ and $U\cup M$ at distance two, so $u+m\le a$, and similarly $v+m\le b$. Such counts involve genuinely nonadjacent witnesses.
- For a mixed vertex $t\in M$, the $k$ anchors exhaust its positive even-distance allowance. Thus its eccentricity is at most three. Every component of $G[P\cup Q\cup T]$ contains a remote. A path between two remotes in different components must meet $A\cup B\cup\{z\}$, which is at distance at least two from each remote. The resulting distance at least four contradicts the eccentricity bound at $t$. Since the induced graph is connected, a missing neighbor of $t$ there would supply a vertex at distance exactly two along a shortest induced-graph path. Thus every member of $M$ sees every other induced-graph vertex. This gives a complete set $M$ with universal incidence to the nonanchor endpoints, without any bound of one on $m$.

## Independent closure checks

On $L=G[X\cup U]$, every anchor has local degree $k-1$, every $p\in P$ has local degree at least $k-m$, and every member of $U$ has local degree at least $k-(v+m)\ge a\ge u+m$. The degree calculations correctly count the possible external sets $\{z\},M,V\cup M$, respectively.

If $u>0$, add a marker adjacent only to $a_0\in A$ and $r_0\in U$. Its augmented graph has order $N=k+u+1$. The [classical cycle-closure step](https://www.sciencedirect.com/science/article/pii/0012365X76900789) applies at each stage.

| Stage | Lower bound on the degree sum when needed |
|---|---|
| Add $a_0r_0$ | $k+(u+m+1)\ge N$ |
| Complete $a_0$ to $U$ and $r_0$ to $A$ | $(k+1)+(u+m)\ge N$ and $(u+m+2)+(k-1)\ge N$ |
| Complete $U$ to $P$ and to $A$ | $(u+m+1)+(k-m)=N$ and $(u+m+1)+k\ge N$ |
| Complete $P$ if $k>u+2m$ | $2(k-m)\ge N$ |
| Complete $P$ if $k=u+2m$ | Then $a=u+m,\ b=m,\ v=0$; after completing $U$ to $P$, $2(a+u)=4u+2m\ge 2u+2m+1=N$ |
| Complete $U$ | Every member sees all $k$ vertices of $X$; $2k\ge N$ because $u\le a\le k-1$ |

The anchor vertices of $X$ are already complete to $X$. The marker remains degree two at every step; removing it after reversing closure gives a spanning path with the exact two prescribed endpoints.

If $u=0$ and $m>0$, use a prescribed endpoint $p_0\in P$. If $2m<k$, all $X$-degrees are at least $k-m$, including anchors since $m\ge1$. Thus $2(k-m)\ge k+1$ gives closure on the marked graph. If $2m=k$, the two parts $A,P$ both have size $m$ and are completely joined; an alternating path can begin at any $a_0$ and end at any $p_0$. The same reasoning on the other side yields its own prescribed endpoints. Use the two endpoints in $P\cup Q\cup U\cup V$ to join through $M$ and close through $z$.

When $m=0$, both $U,V$ are nonempty because $P,Q$ need outer neighbors. Without a $U$-$V$ edge all cross-side paths use $z$. At a remote in $U$, the $a$ anchors of $A$ are at distance two, the $b$ anchors of $B$ are at distance four, and any remote of $V$ is at distance six. Those $k+1$ distinct witnesses force a $U$-$V$ edge, and the two marked paths use that edge's endpoints. The proof also applies at $k=2$, where the balanced $u=0$ case or the closure inequalities remain valid.

The initial count above is independent of the regular split-ball Lemma 2.2 of Asratian–Granholm. That published lemma starts at any cut vertex of any radius-two ball in a regular graph. The irregular proof needs the cut vertex itself to have minimum degree. The manuscript is a paper proof; a Lean proof of the necessary closure and endpoint transfer has not been audited here. [Asratian–Granholm, Lemma 2.2](https://arxiv.org/pdf/2107.07037)

## Moving the split to a minimum-degree cut vertex

The two proofs developed independently by the closure and audit workers agree on the following relocation argument. Suppose $z\ne x$ is a cut vertex of $B_2(x)$. Then $x$ is adjacent to $z$, since a vertex at distance two from $x$ could not be an internal vertex of a shortest path of length at most two from $x$ to any other vertex of its ball. Let $C$ be the component of $B_2(x)-z$ containing $x$, let $A=N(z)\cap C$, and let $B=N(z)\setminus C$. Write $p=|A|,\ q=|B|$, so $p+q=k$, and both are positive. In fact all vertices of $B_2(x)$ lying outside $C\cup\{z\}$ belong to $B$: any shortest path from $x$ to such a vertex has length two and must use $z$.

The neighbors of $x$ outside $N[z]$ form a set $W$ of size at least $k-p=q$, because its only possible other neighbors are $z$ and the other $p-1$ members of $A$. They are all at distance two from $z$. A vertex $b\in B$ has at most $q$ neighbors in $B_2(x)$, namely $z$ and the other $B$ vertices. Hence it has at least $k-q=p$ neighbors $Y$ outside $B_2(x)$. Every such vertex is at distance two from $z$: its edge to $b$ gives the path, and an edge to $z$ would place it in $B_2(x)$. The cap at $z$ enforces $|W|=q$, $|Y|=p$, and $N_2(z)=W\sqcup Y$. Now $x$ must see every other member of $A$ to reach degree $k$. Thus $A\cup W$ is contained in $N[x]$ and no vertex there has a neighbor in $Y$ outside $B_2(x)$. The original split prevents any edge from $A\cup W$ to $B$. So $B_2(z)-z$ is disconnected across the nonempty sets $A\cup W$ and $B\cup Y$.

If instead $z$ is the unique minimum-degree vertex, with $\deg(z)=\delta<\sigma$ in the original conjecture, it cannot cut any ball. For its own ball, each component minus $z$ would have at least $\sigma$ vertices, while there are at most $\delta+\sigma<2\sigma$ vertices available. For a ball centered at a different vertex, the same construction produces disjoint sets of at least $\sigma-p$ and $\sigma-q$ distance-two witnesses at $z$, because $x$ and $b$ have degree at least $\sigma$. Their combined size is at least $2\sigma-\delta>\sigma$.

For comparison, if $\delta=\sigma=k$ and a higher-degree vertex $z$ cuts its own ball, the ball still has exactly two components after deleting $z$. If it had $j\ge3$ components, each has at least $k$ vertices, so $d(z)+k\ge jk$. Any component with $a_i$ neighbors of $z$ contributes $d(z)-a_i$ distance-two witnesses to an anchor in that component. Thus each $a_i\ge d(z)-k$, implying $d(z)\le jk/(j-1)$. This contradicts $d(z)\ge(j-1)k$ for $j\ge3$. With two components, the same distance-two count bounds the number of anchors on each side by $k$. In a 2-connected graph each side must have an edge to the distance-three layer, so each side has an anchor that sees a remote at distance two. This tightens both anchor-size bounds to $k-1$. These inequalities do not give the two component sizes used by the prescribed-endpoint closure.

## The all-2-connected-balls complement

In the finite setting Asratian's local theorem assumes that every radius-two ball is 2-connected and that $d(u)+d(v)\ge |B_2(w)|-1$ on every induced path $u-w-v$. It yields a Hamiltonian graph or a graph containing a spanning $K_{p,p+1}$, which already has a Hamiltonian path. The separate Asratian–Khachatryan theorem uses $d(u)+d(v)\ge|N(u)\cup N(w)\cup N(v)|$ instead and yields a Hamiltonian cycle. These are independent published sufficient criteria, restated as Theorems 1.4 and 1.3 in the later Asratian–Granholm–Khachatryan paper. [Finite local theorems](https://arxiv.org/pdf/1810.07023)

A sufficient degree-slack implication is immediate from the Graph 189 cap. If $z$ is the unique vertex of degree $\delta<\sigma$, any induced $u-w-v$ has $d(u)+d(v)\ge2\sigma-(\sigma-\delta)\mathbf1_{w\sim z}$. Also $|B_2(w)|-1=d(w)+|N_2(w)|$ and $|N_2(w)|+|N_4(w)|\le\sigma$. Thus the radius-two theorem applies if every ball is 2-connected and
$$
d(w)+(\sigma-\delta)\mathbf1_{w\sim z}\le\sigma+|N_4(w)|
$$
for every $w$. The analogous bound with the penalty set to zero applies when $\delta=\sigma$. This is a sufficient subfamily, not a deduction of the local degree sum from the original hypotheses.

### An infinite obstruction to applying either published criterion automatically

Use the seven-vertex base identified by the formalize worker with edges
$$
02,03,04,06,12,15,23,25,34,36.
$$
Replace each base vertex by a clique of size $t$, except role 2 which receives a clique of size $2t-1$, where $t\ge2$. Join fibers completely along base edges. Distances between fibers equal the base distances, because paths lift and projecting paths to base walks and suppressing consecutive repetitions cannot decrease the lower bound from the base metric. Distinct vertices in the same fiber are adjacent. The nonuniform expansion therefore has order $8t-1$, diameter three, and the following degree and positive even-distance counts.

| Roles | Degree | Positive even-distance count |
|---|---:|---:|
| 0, 2, 3 | $6t-2$ | $2t$ |
| 1, 5 | $4t-2$ | $2t$ |
| 4, 6 | $3t-1$ | $3t-1$ |

In particular $\delta=\sigma=3t-1$, the original even-distance cap holds, and $n>2\sigma+3$. Every radius-two ball consists of all fibers of a connected base radius-two ball. Each fiber still has at least one vertex after deletion of a single vertex, so those balls are 2-connected. Take the induced path with vertices from roles $4,0,6$. The endpoint degree sum is $6t-2$, but the union of the three neighborhoods consists of roles $0,2,3,4,6$ and has size $6t-1$. The radius-two ball at role 0 is the whole graph, so its order minus one is $8t-2$. Both published local degree conditions fail at this path.

These graphs satisfy the exact triangle-bearing large-minimum-degree leaf $\mathrm{R1.H1.R1.H2}$. In particular they have a Hamiltonian cycle: split each of the fibers 2, 0 and 3 into two nonempty groups, and traverse
$$
2_a,\ 1,\ 5,\ 2_b,\ 0_a,\ 4,\ 3_a,\ 6,\ 0_b,\ 3_b,\ 2_a,
$$
visiting each group in any internal order. The cycle successor sends any independent set injectively into its neighborhood. This demonstrates a limitation of both published sufficient criteria in the exact residual, while the graph itself is traceable. The base and unequal-expansion obstruction were checked by elementary counts; independent breadth-first searches confirmed the base and checked the unequal expansion for $2\le t\le8$, including every one-vertex deletion in each radius-two ball and the displayed Hamiltonian cycle.

## Current upstream scope

The live merged-PR search found [#2971](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2971), [#5336](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5336) and [#6181](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6181). The matching open-PR search returned no result. #6181 is a reduction of the diameter-four-or-five step. It proves the triangle-free subcase in its own checked module and leaves separate diameter-four and diameter-five cases with triangles. This is consistent with the global triangle-free theorem already established internally in #5336. The externally submitted [PR #70](https://github.com/umaia1234/agentic-conjectures/pull/70) remains a partial low-$\sigma$ computational result, distinct from these reductions.

| Exact unresolved reduction input in the audited tree | Additional graph premises |
|---|---|
| $\mathrm{R1.H1.R1.H1}$ | Diameter three, a triangle, $\delta\le2$ |
| $\mathrm{R1.H1.R1.H2}$ | Diameter three, a triangle, $\delta\ge3$ |
| $\mathrm{R1.H2.R1.H1}$ | Diameter four, a triangle |
| $\mathrm{R1.H2.R1.H2}$ | Diameter five, a triangle, every distance-five pair has an endpoint of degree less than $\sigma$ |

All leaves retain connectedness, $\delta+\sigma+1<n\le(\delta+1)(\sigma+1)$, the original full even-distance bound, and the neighborhood condition on every independent set. The irregular split-ball theorem establishes a paper-level subfamily under $\delta=\sigma$; the all-balls local obstruction explains why a direct appeal to either published Asratian theorem does not discharge the complementary leaves. No current result here supplies every input to the composed kernel proof.
