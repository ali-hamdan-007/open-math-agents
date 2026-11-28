# Traceability through order four times the second-smallest degree

Let $G$ satisfy Graph 189, with second-smallest degree $k$, order $n\le4k$, and vertex connectivity at least three. Then $G$ has a Hamiltonian path. This extends the [earlier moderate-order argument](../root/moderate-order.md) to the smaller values of $k$ by choosing attachment paths that avoid the one possible obstructed terminal pair.

The previously settled cases permit $k\ge6$. Suppose $G$ is nontraceable and take a longest path $P$. The [almost-spanning theorem](../lowblock/all-near-spanning.md) ensures that some exterior component $C$ contains a vertex of degree at least $k$. Write $h=\lceil k/2\rceil$. We use the previously established unrooted exterior facts that every such high vertex has at least $h$ neighbors inside its exterior component and that every high-containing exterior component has order at least $h+2$. These are the even and odd exterior-component results from the preceding checkpoint, as recorded in the [near-degree exterior note](../global/near-degree-exterior.md).

## A 2-connected exterior component

Suppose $C$ is 2-connected of order $m\le k-2$. The [degree-two marker argument](../lowblock/high-connectivity-complete.md) gives a spanning path in $C$ between any specified pair except possibly the two internal neighbors of the unique low vertex when it has internal degree two. Indeed, adding a degree-two marker for the endpoints allows Hamiltonian closure to complete the high part, since $2h\ge m+1$. In the resulting clique on the high vertices the low vertex can be inserted between two of its neighbors except for this possible terminal pair. A Hamiltonian cycle of $C$ also follows from Fan's circumference theorem, because every distance-two pair in $C$ has a high member of internal degree at least $h$.

Put $a=k-m+1$. Exclude the possible low vertex and, if there is an exceptional terminal pair, one of its members. At least $m-2\ge a$ high vertices remain, by $m\ge h+2$. Each has at least $a$ contacts on $P$. Choose $a$ such vertices and greedily assign distinct contacts to them. At each step at most $a-1$ contacts have been used. Any two of these matched exterior terminals can be joined by a spanning path of $C$, and each terminal can start a spanning path by opening a spanning cycle at that vertex.

Every gap and both outer tails of $P$ cut out by the $a$ matched contacts must therefore contain at least $m$ unmarked vertices. Otherwise replace it by a path through $C$ using the relevant matched contacts to extend $P$. Counting also $C$ and the marks gives

$$
n\ge (a+2)m+a=m(k-m+3)+k-m+1.
$$

The expression is concave in $m$. For $k=6,7$ the interval $h+2\le m\le k-2$ is empty. For $k\ge8$, its value at $m=k-2$ is $5k-7>4k$. At $m=h+2$, subtracting $4k$ gives $t^2-4t+1$ when $k=2t$, and $t^2-3t-2$ when $k=2t+1$. Both are positive for the relevant $t\ge4$. This rules out $m\le k-2$.

## An exterior component with a cut vertex

Choose a leaf block $B$ of $C$ whose noncut vertices are all high, possible because the two leaf interiors are disjoint and at most one vertex is low. Let $w$ be its cut vertex and $b=|B|$. A bridge leaf is impossible because its noncut vertex would have internal degree one. Thus $B$ is 2-connected, and $b\ge h+1$.

Suppose $b\le k-2$, and let $R=C\setminus B$. The set $R$ contains a high vertex. Otherwise it consists of the unique low vertex, whose only neighbor in $C$ is $w$. By the [exterior contact bound](../root/exterior-triangle.md), this low leaf has at most one contact on $P$, giving total degree at most two, a previously settled case.

There is a path starting at $w$ that takes at least $h-1$ vertices from $R$. To see this, take a shortest path from $w$ to a high vertex of $R$ staying in $R\cup\{w\}$. Its interior contains no high vertex of $R$. Every high vertex of $R$ has at least $h-2$ high neighbors in $R$, because it loses at most $w$ and the one possible low vertex from its neighborhood in $C$. Inside the high component reached by the shortest path, a longest path rooted at its entry vertex has at least $h-1$ vertices by its endpoint degree. Concatenate these paths. In particular $|R|\ge h-1$.

The graph $B-w$ is Hamilton-connected because its minimum degree is at least $h-1$ and $2(h-1)\ge b=|B-w|+1$. Put $a=k-b+1$. At least $a$ distinct vertices of $B-w$ can be matched to distinct contacts on $P$, since $b-1\ge a$ and each has at least $a$ contacts. Interior gaps can be replaced by spanning routes across $B-w$, giving at least $b-1$ unmarked vertices in every such gap. For each of the two tails, start at its matched port, traverse $B-w$ ending at a different neighbor of $w$ (available because $B$ is 2-connected), and then take $w$ and the path into $R$. This gives at least $(b-1)+h$ unmarked vertices in both tails. Counting all of $C$ gives

$$
\begin{aligned}
n&\ge b+|R|+a+(a+1)(b-1)+2h\\
&\ge b(k-b+3)+3h-2.
\end{aligned}
$$

As a function of $b$ this is concave. At $b=k-2$ its value is $5k+3h-12>4k$. At $b=h+1$, subtracting $4k$ gives $t(t-2)>0$ for $k=2t$ and $t^2-t+1>0$ for $k=2t+1$. This rules out $b\le k-2$.

## A large cycle and three contacts

In either case the 2-connected component or the chosen leaf block has order at least $k-1$, and all but at most one vertex have internal degree at least $h$. Fan's theorem supplies a cycle of length $d\ge k-1$ disjoint from $P$. By 3-connectivity and Menger's theorem there are three vertex-disjoint paths linking the cycle to $P$ with distinct endpoints on both. Trim their interiors off the cycle and $P$.

At each of the two outer tails, a connector permits traversal of the entire cycle. Both internal gaps can use a longer arc of the cycle between the respective connector endpoints, containing at least $\lceil d/2\rceil+1$ cycle vertices. Ordered along $P$, these three marks, the two tails, two gaps, and the exterior cycle give

$$
n\ge 3d+3+2(\lceil d/2\rceil+1)\ge4k+1.
$$

This contradicts $n\le4k$.
