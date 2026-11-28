# Spanning paths in a four-gateway component with small matching slack

Let $G$ be a finite simple 2-connected graph satisfying the Graph 189 hypotheses, and let $k\ge10$ be its second-smallest degree. Suppose $S$ has two components of $G-S$, each with the following properties.

- The component has at most four gateways, where a gateway is a vertex with a neighbor in $S$.
- The component has exactly two distinct neighbors in $S$, and they are nonadjacent.
- Every edge from the component to $S$ lies in a triangle.
- The component contains a vertex of degree at least $k$ that is not a gateway.

Then at least one of the two components has a spanning path whose two endpoints can be joined to its two different exterior neighbors.

## A component with slack at most one

Use the [gateway matching notation](gateway-matching-defect.md). The maximum matching from each gateway set to $S$ has size two by 2-connectivity and the two-neighbor condition. Its defect is therefore at most two. The two row slacks from that argument satisfy

$$
r_1+r_2=\delta_1+\delta_2+\epsilon_1+\epsilon_2-2\le3.
$$

At least one row has slack at most one. A tight row already yields a spanning path between any pair of distinct gateways by the cited argument, since the gateway count is at most $\lfloor k/2\rfloor$. A size-two matching to $S$ then gives a compatible pair of endpoints.

Assume the remaining row has slack one. Write $C$ for that component, $b$ for its gateway count, and $H$ for its high nongateways, where high means degree at least $k$. Let $\eta=|C|-1-k\ge0$. Fix a maximum gateway matching, with two matched gateways. For any $x\in H$, the proof of the defect bound reserves the foreign high nongateways at distance four and at least $2-\eta$ separator vertices at distance two. The difference between these lower bounds and the cap is one.

In fact every $x\in H$ is adjacent to every other vertex of $C$ except possibly the matched gateways. Otherwise $x$ misses a vertex other than those gateways. Since it misses at most $\eta$ vertices in $C$, it then misses at most $\eta-1$ matched gateways and reaches at least $3-\eta$ separator vertices at distance two. The slack would be used entirely, leaving no distance-two vertex in $C$. But an internal shortest path to the nonneighbor gives such a vertex. In particular, $H$ is a clique, it is joined to every unmatched gateway, and it is joined to the possible low nongateway. Also $|H|\ge k-b\ge6$ because $|C|\ge k+1$.

Call a gateway active if it has a neighbor in $H$. A high vertex $x\in H$ is at distance two from every active gateway it misses: a neighbor of that gateway in the clique $H$ supplies a path of length two. As the row has slack one, $x$ can miss at most one active gateway. Any inactive gateway must be matched and has degree at most $(b-1)+1+2\le6$, counting other gateways, the possible low nongateway, and the two exterior neighbors. Thus an inactive gateway is below degree $k$, so at most one exists.

Let $p,q$ be the two exterior neighbors of $C$. Each has at least two gateway neighbors. Indeed, for any edge from $p$ to a gateway, a third vertex of a triangle must lie in $C$, because $q$ is the only possible third vertex in $S$ and is nonadjacent to $p$. The same holds for $q$.

## All gateways active

The neighbor sets within $H$ of the two matched gateways cover $H$, because each vertex of $H$ misses at most one active gateway. Thus at most one matched gateway can have exactly one neighbor in $H$. If there is such a gateway, use it as one endpoint, attached to one of its exterior neighbors, and choose a distinct gateway attached to the other exterior neighbor as the opposite endpoint. If no gateway has only one neighbor in $H$, choose compatible endpoints from a matching of size two.

List the gateways in any order between these endpoints. Reserve one vertex of $H$ for each endpoint gateway and two for each interior gateway, using distinct reserved vertices and choosing them from the gateway's neighbors. For the matched gateways this is possible because each has enough neighbors individually, and their neighbor sets together cover at least six vertices of $H$, more than their combined demand of at most four. Every unmatched gateway is joined to all of $H$, and the total demand is $2b-2\le6$, so allocate the remaining reservations freely. In every gap, place the reserved vertices for the two adjacent gateways next to those gateways. They are joined since $H$ is a clique. Any remaining vertices of $H$, and the possible low nongateway, can go between two reserved vertices in a gap, with the low vertex surrounded by vertices of $H$. This gives the required spanning path.

## One inactive gateway

Let $g$ be the inactive gateway. It is the only below-$k$ vertex, so there is no low nongateway in $C$. If there are only two gateways, then both are adjacent to both exterior neighbors because each exterior neighbor has at least two gateway neighbors. The inactive vertex $g$ is adjacent within the component to the other gateway $h$, since $C$ is connected. Any vertex of $H$ adjacent to $h$ has $g$ and both exterior neighbors at distance two. Such a vertex exists because $h$ is active; otherwise no high nongateway could be at distance two from $S$, despite its distance at most four to a foreign high nongateway. Also $\eta\ge1$ because every vertex of $H$ misses $g$. The two exterior neighbors already exceed the reserved lower bound $2-\eta$ by at least one, and the additional vertex $g$ exceeds the remaining slack. This is impossible.

There are therefore at least three gateways. As $C$ is connected, $g$ has an active gateway neighbor. If $g$ has an unmatched gateway neighbor, choose one as $h_0$. It is adjacent to all of $H$, so every vertex of $H$ sees $g$ at distance two. Hence no vertex of $H$ can also miss the other matched gateway, which is active and would then be an additional distance-two vertex. In this case all active gateways are adjacent to every vertex of $H$. Otherwise $g$ has exactly one possible internal neighbor, namely the other matched gateway. Choose that active gateway as $h_0$. All other active gateways are unmatched and adjacent to every vertex of $H$.

There is an unused gateway $e\notin\{g,h_0\}$ that can be joined to an exterior neighbor different from one chosen for $g$. If $g$ sees only one exterior neighbor, the other has at least two gateway neighbors and at most one is $h_0$. If $g$ sees both, choose any unused gateway and use the opposite exterior neighbor for $g$. Now build a spanning path on the active gateways and $H$ with endpoints $h_0,e$, then prefix $g$ using the edge $gh_0$. The construction is the same gap allocation as before. The only possible active gateway with restricted neighbors in $H$ is $h_0$, now an endpoint, so only one neighbor needs to be reserved for it. This gives the required spanning path from $g$ to $e$.
