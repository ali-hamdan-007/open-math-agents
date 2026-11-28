# Connector-pruned tough block constructions

In a qualifying connected graph, let $k$ be its second-smallest degree. Call a vertex of degree at least $k$ high. The Graph 189 even-distance cap is $k$, and two high vertices are at distance at most four by the established distance bound.

## Two satellites per marked lobe

Partition the vertices into a set $T$ of $\ell$ connectors and lobes. Each lobe has two specified gates. All gates form a clique, and they account for all edges between distinct lobes. Edges incident with $T$ are arbitrary. Mark $m\ge 2\ell+3$ lobes, each with two disjoint, nonempty satellite sets. Every satellite vertex is anticomplete to the gates and has at most $\ell+3$ neighbors within its lobe outside its own satellite set. Suppose some high nongate vertex has a gate neighbor outside $T$. Under these conditions the graph cannot qualify.

That high nongate vertex sees the gates of all other marked lobes at distance two, so
$$
k\ge 2(m-1)\ge 4\ell+4.
$$
A satellite containing a high vertex has size at least
$$
q:=k-2\ell-2\ge k/2,
$$
since even a high vertex has at most $2\ell+3$ neighbors outside its satellite. For any $r$ selected marked lobes, at most one vertex of their combined satellite sets is low. Their combined number of high satellite vertices is therefore at least $(2r-1)q$. If one satellite has no high vertices, it uses the one low vertex and the other $2r-1$ satellites consist entirely of high vertices of sets of size at least $q$. Otherwise all $2r$ sets have size at least $q$ and at most one low vertex in total.

Call a connector exclusive if its high satellite neighbors in the marked lobes meet exactly one marked lobe. Let $e$ be the number of exclusive connectors and discard the at most $e$ marked lobes they meet. A connector meeting high satellites in at least two marked lobes has at most $2k$ such neighbors. In fact, if it meets $b\ge 2$ lobes and has $p_i$ high satellite neighbors in lobe $i$, any one of those neighbors sees all the other $\sum_{j\ne i}p_j$ at distance two. Therefore $(b-1)\sum_jp_j\le bk$. In the remaining marked lobes, at most $2(\ell-e)k$ high satellite vertices have a connector neighbor.

Two high satellite vertices from different lobes that both lack connector neighbors necessarily have distance four. They have no neighbors outside their own lobe, no gate neighbors, and there are no edges between the nongates of distinct lobes. Thus they have no path of length at most three, and the high-endpoint distance bound gives four. If any high satellite vertex without a connector neighbor remains, discard its lobe. Its even-distance cap leaves at most $k$ such vertices in the remaining marked lobes. If no such vertex remains, the same bound is automatic.

There are now $r\ge m-e-1$ marked lobes. Their high satellite count is bounded below by
$$
(2r-1)q\ge (4\ell+3-2e)k/2
$$
and above by $(2(\ell-e)+1)k$. The lower bound exceeds the upper bound by at least $(e+1/2)k$.

## Application to the standard rooted tough obstruction

In the Bauer–Broersma–Veldman construction, the basic lobe has gates $u,v$, an internal square $a,b,d,c$ in cyclic order, a top satellite adjacent to $a,b$ and a bottom satellite adjacent to $c,d$. The gate $u$ is adjacent to $a,c$, and $v$ is adjacent to $b,d$. The graph obtained by completing the gates into a clique and adding a universal connector clique is nontraceable when the number of these lobes is at least $2\ell+3$. [Bauer, Broersma and Veldman (2000), Theorem 3 and Figure 1](https://research.utwente.nl/files/6708998/Bauer00not.pdf)

Allow positive clique weights on both satellites and on all four square corners of a lobe, retaining singleton gates. With all four corners singletons, the lobe has no spanning path with endpoints $u,v$. Each satellite must appear as one run, since two runs at the same satellite would force a cycle through its two singleton neighboring corners. Contracting the two runs thus prescribes the use of $ab$ and $cd$. Joining these two sections via $ac$ leaves open ends $b,d$, both on the $v$ side. Joining them via $bd$ leaves open ends $a,c$, both on the $u$ side. Neither gives endpoints $u,v$. If any corner has weight at least two, there is a rooted spanning path. For example, when $a$ has weight at least two, use the vertex types
$$
u,a,\text{top},b,a,c,\text{bottom},d,v.
$$
Expand the satellite runs and insert every surplus corner vertex next to an existing vertex of the same type. Symmetries preserving the unordered gate pair carry $a$ to any corner.

To certify nontraceability whenever at least $2\ell+3$ lobes have singleton corners, take a putative spanning path and delete $T$. This leaves at most $\ell+1$ path pieces and at most $2\ell+2$ ends. Each lobe without a rooted spanning path must contain an end. Otherwise its runs along the path pieces can enter and exit only through its two gates. A run containing a nongate must use both gates, leaving that run as a spanning path of the lobe between its gates. This contradicts the local obstruction.

Regardless of how edges incident with $T$ were pruned, each such lobe is a marked lobe for the two-satellite theorem. Its satellites have only two own-lobe neighbors outside their satellite. There is a high corner adjacent to a gate, since there are four corners in each marked lobe and at most one low vertex. Thus the Graph 189 hypotheses fail throughout this weighted, connector-pruned family for every parameter choice certified nontraceable by the rooted lobe count. The obstruction applies even with additional lobes of arbitrary structure that respect the same private-gate condition.
