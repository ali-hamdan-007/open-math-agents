# Matching deficits for components with internal vertices in Graph 189

Let $G$ be a finite simple 2-connected graph satisfying the Graph 189 hypotheses, and write $k$ for its second-smallest degree. Call vertices of degree at least $k$ high. We use the established fact that any two high vertices are at distance at most four.

Fix any vertex set $S$, and choose $t\ge2$ components $C_1,\ldots,C_t$ of $G-S$, each containing a high vertex with no neighbor in $S$. For each $i$, let $B_i$ be the vertices of $C_i$ with a neighbor in $S$, let $b_i=|B_i|$, and let $D_i=|C_i\setminus B_i|$. Let $\epsilon_i$ be the number of below-$k$ vertices in $C_i\setminus B_i$, so $D_i-\epsilon_i$ counts the high vertices in this set. Let $\nu_i$ be the maximum matching size between $B_i$ and $S$ via the edges of $G$, and put $\delta_i=b_i-\nu_i$.

For a high vertex $x$ in $C_i\setminus B_i$, all its neighbors lie in $C_i$. It misses at most $|C_i|-1-k$ other vertices of $C_i$, and in particular misses at most that many of the gateways used in a matching of size $\nu_i$. The remaining matched gateways give distinct vertices of $S$ at distance two from $x$. Thus

$$
|N_2(x)\cap S|\ge \nu_i-(|C_i|-1-k)=k+1-D_i-\delta_i.
$$

Every high vertex in $C_j\setminus B_j$, for $j\ne i$, is at distance four from $x$: a path must cross $S$ and each endpoint has distance at least two from $S$, while the high-endpoint bound gives distance at most four. These witnesses and the separator witnesses are disjoint. The even-distance cap implies

$$
D_i+\delta_i\ge1+\sum_{j\ne i}(D_j-\epsilon_j).
$$

Consequently the total deficiency obeys

$$
\sum_i\delta_i
\ge t+(t-2)\sum_i(D_i-\epsilon_i)-\sum_i\epsilon_i
\ge t(t-1)-1.
$$

In particular, two components cannot both have a matching from all their gateways into $S$, regardless of the number of gateways. The special case of two gateways follows because each component has at least two distinct neighbors in $S$ by 2-connectivity, so its two gateways can be matched to different vertices.

## Tight rows yield spanning paths between gateways

For $t=2$, put $r_i=D_i+\delta_i-(D_j-\epsilon_j)-1$ for $j\ne i$. Then each $r_i\ge0$, and

$$
r_1+r_2=\delta_1+\delta_2+\epsilon_1+\epsilon_2-2.
$$

If $r_i=0$, the lower bounds above exhaust the cap at every high vertex $x$ of $C_i\setminus B_i$. Thus $x$ has no vertex of $C_i$ at distance two, and is adjacent to every other vertex of $C_i$: otherwise a shortest path inside the connected component to a nonneighbor gives a vertex at graph distance two. In particular $x$ is adjacent to all $\nu_i$ matched gateways. Equality in the separator-witness bound therefore gives $|C_i|=k+1$ and $|N_2(x)\cap S|=\nu_i$.

If $b_i\le\lfloor k/2\rfloor$, the tight component admits a spanning path between every pair of distinct gateways. List the $b_i$ gateways with the two prescribed endpoints first and last. The $k+1-b_i-\epsilon_i$ high vertices of $C_i\setminus B_i$ are adjacent to all of $C_i$. Use them to fill the $b_i-1$ gaps with one or more vertices each. If there is a below-$k$ vertex of $C_i\setminus B_i$, surround it with two high vertices in one of those gaps, which is possible since $k+1-b_i-\epsilon_i\ge b_i$ when $\epsilon_i=1$.

It follows that if both components lack a spanning path between some prescribed pair of distinct gateways and each has at most $\lfloor k/2\rfloor$ gateways, then both $r_i\ge1$, so

$$
\delta_1+\delta_2\ge4-\epsilon_1-\epsilon_2.
$$

For $k\ge6$, this excludes any two such components with at most three gateways each. In a 2-connected graph the gateway incidence of any component, when there are at least two components after deletion, has a matching of size at least two. Each side has at least two vertices incident to some edge, and only a star can have maximum matching size one. Hence each $\delta_i\le1$ for at most three gateways, whereas $4-\epsilon_1-\epsilon_2\ge3$.
