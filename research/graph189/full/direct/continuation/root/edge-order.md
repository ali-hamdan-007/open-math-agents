# Order from the common neighbors of any one edge

Let a finite connected simple graph have at most k other vertices at positive even distance from each vertex. For any edge xy, let c be its number of common neighbors and d the larger endpoint degree. Then

    n ≤ 2k+2+c + k(k+1+c−d).

This holds without an assumption on minimum degree, connectivity beyond connectedness, or diameter. For Graph 189, at least one endpoint is high, so every edge belongs to at least ⌈(n−3k−2)/(k+1)⌉ triangles. In particular an edge in no triangle forces n≤3k+2, even if the graph has a cut vertex.

**Argument.** Set U=N[x]∪N[y]. Its size is d(x)+d(y)−c. Let E_x be the vertices outside U at even distance from x, and define E_y symmetrically. Exactly d(y)−1−c members of U are at positive even distance from x: these are the neighbors of y other than x which do not neighbor x. Thus |E_x|≤k+1+c−d(y), with the analogous estimate for E_y.

Every vertex outside U∪E_x∪E_y has odd distance at least three from both endpoints. On a shortest path from x to such a target, the penultimate vertex a is at even distance from x and belongs to E_x. Membership of a in U would put the target within distance two of x or y. Assign the target to a. For each a used, fix a predecessor b of a on a shortest path from x. Every target assigned to a belongs to the distance-two layer of b: the two-edge route via a realizes the lower bound given by their layers from x. There are at most k targets per a. Starting at y instead gives the same bound using E_y. Counting U, the two even sets and at most k·min(|E_x|,|E_y|) remaining vertices proves the inequality.

Combining this result with the [path contact count](exterior-triangle.md), let c_C count the neighbors inside C common to two adjacent high vertices outside a longest path, and let e=max(d(x),d(y))−k. Their common neighbors on the path number at most c_C+1−e. Substituting c≤2c_C+1−e in the edge order inequality gives

    n ≤ 4k+3+2(k+1)c_C−(2k+1)e.

Together with the interior triangle theorem, every such edge has at least max(1,⌈(n−4k−3+(2k+1)e)/(2k+2)⌉) common neighbors within the component. These are necessary properties for a counterexample of large order. Independent paper audit by gpt-6.2-astra.
