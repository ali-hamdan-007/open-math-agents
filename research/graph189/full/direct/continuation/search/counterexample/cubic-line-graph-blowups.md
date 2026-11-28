# Blow-ups of line graphs of triangle-free cubic graphs

Let $H$ be a finite simple connected triangle-free cubic graph. Replace every vertex of its line graph $L(H)$ by a nonempty clique or independent set, with complete joins over line-graph edges and no other joins. Every resulting graph satisfying Graph 189 is traceable. Unless $H=K_{3,3}$, no such blow-up satisfies the even-distance bound at its second-smallest degree.

Write $d_L$ for line-graph distance. For an edge $e=uv$ of $H$, write $a,b$ for the other neighbors of $u$ and $c,d$ for the other neighbors of $v$. They are distinct by triangle freeness. The four line neighbors of $e$ supply eight incidences to line vertices at distance two, two at each remote endpoint. The only duplications arise from edges between $\{a,b\}$ and $\{c,d\}$. If there are $s$ such cross edges, the second layer of $e$ therefore has size $8-s$. For $s\le2$ it supplies at least six positive even-distance vertices. For $s=4$, the six vertices already form a cubic $K_{3,3}$, so connectedness gives $H=K_{3,3}$.

Now suppose $s=3$. These six vertices induce $K_{3,3}$ minus one edge. The two deficient vertices have one exit edge each, and there are no other exits. The exterior vertex count is positive and even because $H$ is cubic. If the exterior has $x$ vertices it spans $(3x-2)/2$ edges. At $x=2$ this would require two edges in a simple graph on two vertices. At $x=4$ it would require five edges, which forces a triangle on four vertices. Consequently $x\ge 6$ and $H$ has at least eighteen edges. Both exit edges have line-graph distance two from $e$. Every other exterior edge at distance at most three touches the exterior endpoint of an exit edge, so there are at most four such edges. The ball of radius three at $e$ contains at most fourteen vertices of $L(H)$, counting the eight block edges, two exits, and four other exterior edges. Connectedness now supplies a line vertex at exact distance four. Along with the five at distance two, this gives at least six positive even-distance vertices for $e$.

For $H\ne K_{3,3}$, put $m=|E(H)|$ and write $w_f$ for the positive fiber size of each $f\in V(L(H))$. Distances between distinct fibers are exactly the base distances. If $D_f$ is the degree of one vertex of fiber $f$ and $E_f$ its positive even-distance count, then
$$
D_f+1\le\sum_{g\in N_L[f]} w_g,
\qquad
E_f\ge\sum_{\substack{g\ne f\\d_L(f,g)\text{ even}}}w_g.
$$
Each closed neighborhood of $L(H)$ has size five. The even-distance relation is symmetric and each line vertex has at least six positive even-distance line vertices. Summing, if the blow-up qualified with second-smallest degree $k$, would give
$$
mk\ge\sum_f E_f\ge6\sum_f w_f
\ge \frac65\sum_f(D_f+1)
\ge \frac65\bigl((m-1)k+m\bigr)>mk.
$$
The final inequality uses $m\ge 6$. At most one fiber can have degree below $k$ because all vertices of the same fiber have equal degree.

For $H=K_{3,3}$, the line graph and all the allowed blow-ups have diameter at most two. Every nonneighbor of a minimum-degree vertex is then at distance two, so the minimum degree $\delta$ satisfies $\delta+k\ge n-1$. Any two distinct vertices have degree sum at least $\delta+k$. Adjoining a universal vertex gives the usual Ore degree-sum condition for a Hamilton cycle, which yields a spanning path when the new vertex is deleted.

## Triangle expansions of cubic cores

The same weighted exclusion holds for $L(H)$ if $H$ is obtained from a connected simple cubic graph $F$ by replacing each vertex in some set by a triangle and putting its three old incidences at three distinct triangle vertices, under either of these conditions.

- Every vertex of $F$ is expanded.
- $F$ has girth at least five.

Let an external edge be one joining distinct original vertex modules. An original module is either a singleton or an expanded triangle. No external edge has a common neighbor of its two endpoints under either condition. The four remote endpoints reached from an external edge by following one additional edge are therefore distinct. They supply eight incidences to exact distance-two line vertices, with any duplication arising only from an edge between remote endpoints.

If every vertex of $F$ is expanded, the only possible duplication edges are the two inside the endpoint triangles. Under the girth assumption, a duplication edge with endpoints on the same side can likewise occur only inside an expanded module, since any other such edge would project to a triangle. A cross duplication would project to a triangle or four-cycle if either endpoint module is unexpanded. When both modules are expanded it would require a second edge between the same two modules. Thus every external edge has at least six second-layer witnesses in either case.

For an internal edge $uv$ of an expanded triangle with third vertex $w$, let $a,b,c$ be the external neighbors of $u,v,w$. They lie in distinct modules. The edge $wc$, the two other edges at $a$, and the two other edges at $b$ supply five distinct second-layer witnesses. Distinctness follows because $a$ and $b$ cannot be adjacent. If all modules are expanded, each of $a,b$ has already used its sole external edge. Under the girth assumption, any adjacency between their modules would project to a triangle.

When all modules are expanded, take the edge of the $c$-triangle opposite $c$. Every path of length at most two from $u$ or $v$ stays outside that pair of opposite vertices. Taking its first step inside the $uv$-triangle can reach $c$ only on the second step. Taking its first step outside the $uv$-triangle reaches $a$ or $b$, neither of which can reach the $c$-triangle on the second step since their only external edge goes back. There is a length-three path through $w,c$ to each opposite vertex. Thus the opposite edge has line-graph distance exactly four from $uv$.

For the girth condition, the vertex ball of radius two from the set $\{u,v\}$ has ten vertices. They are $u,v,w,a,b,c$ and the two other neighbors of each of $a,b$. A coincidence among those last four vertices or with the first six would induce a triangle or four-cycle in $F$, except that neighbors of $a$ or of $b$ may lie in the same expanded module as their own parent, in which case the triangle vertices themselves are distinct. The ball spans at least ten edges, counting the three sides of $uvw$, the three exits of that triangle and the four other edges at $a,b$. As a result at most ten edges leave the ball. If $H$ has order at least fourteen, cubicity implies that some edge has both endpoints outside this ball. Its distance in the line graph from $uv$ is at least four, so a shortest line-graph path to it supplies a vertex at exact distance four.

The six-witness sum from the first part now handles the fully expanded case and the girth case at inflated orders at least fourteen. If there are no expansions under the girth condition, the first part already applies. Otherwise the girth-five ball of radius two about any vertex of $F$ has ten distinct vertices, and expanding one vertex adds two vertices. The only remaining order is twelve, with one expanded triangle. All line vertices have at least five positive even-distance line vertices, and every line vertex except potentially the three inner edges of the expanded triangle has at least six. Let $W$ be the total fiber weight and $W_6$ the weight outside those three inner fibers. The even-count sum and degree sum now imply
$$
mk \ge 5W+W_6 \ge (m-1)k+m+W_6.
$$
Remove the three inner line vertices and their three external line neighbors from consideration as centers. Of the $m=18$ line vertices at least twelve remain, so one such center has degree at least $k$ in the blow-up. Its closed line neighborhood contains only fibers counted in $W_6$ and consequently has total weight at least $k+1$. This contradicts $W_6\le k-m$.
