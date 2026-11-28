# Reciprocal incidence bounds for component-count obstructions

Let $G$ be a finite simple 2-connected graph satisfying the Graph 189 even-distance bound, with second-smallest degree $k$. For a vertex set $S$, the width of a component of $G-S$ is the number of distinct neighbors of the component in $S$. Suppose every component has width at most $b$. The following conditions imply $c(G-S)\le |S|+1$.

| Maximum width $b$ | Degree threshold | Threshold if every width-two component has nonadjacent exterior neighbors |
| --- | --- | --- |
| 2 | $k\ge4$ | $k\ge3$ |
| 3 | $k\ge8$ | $k\ge6$ |
| 4 | $k\ge10$ | $k\ge8$ |
| 5 | $k\ge12$ | $k\ge10$ |
| $b\ge6$ | $5k>12(b-1)$ | $5k>12(b-1)$ |

There is no minimality assumption on $S$ or structural assumption on the components. The extra condition is automatic for a hypothetical Graph 189 counterexample by the known traceability result for an adjacent separating pair.

## Reciprocal incidence

Suppose instead that $c(G-S)\ge |S|+2$. Discard the possible component containing the unique below-$k$ vertex. There are at least $|S|+1$ wholly high components. A component of width $w$ contributes $1/w$ to each of its $w$ exterior neighbors, so the total over $S$ exceeds $|S|$. Some $u\in S$ therefore receives total greater than one. Every width is at least two by 2-connectivity, so $u$ meets at least three wholly high components.

If it meets four, the [distance-two counts](bounded-exterior-attachments.md) for those four give

$$
4(k+1-b)\le \left\lfloor\frac{4k}{3}\right\rfloor+k.
$$

This implies $5k\le12(b-1)$ and is incompatible with every threshold in the table. Thus $u$ meets exactly three wholly high components. Write their widths in nondecreasing order as $w_1,w_2,w_3$, and put $W=w_1+w_2+w_3$. If the reciprocal sum exceeds one, either there are two widths equal to two, or the widths are $(2,3,j)$ for $3\le j\le5$. Indeed, three widths at least three contribute at most one, and if the smallest is two and the other two are at least four they also contribute at most one. With widths two and three, the third reciprocal must strictly exceed $1/6$.

Therefore the largest possible $W$ for such a triple is $6,8,9,10$ for $b=2,3,4,5$, respectively, and at most $b+4$ for $b\ge6$.

## Small excess in the three-component count

For $i=1,2,3$ define $a_i=|N(u)\cap C_i|$ and $X_i=|N_2(u)\cap C_i|$. Write $A=\sum_i a_i$, $M=\lfloor3k/2\rfloor$, and $e=W-3-\lceil k/2\rceil$. The earlier counts give

$$
A-a_i\le k,\qquad A\le M,\qquad \sum_i X_i\le k,\qquad
a_i+X_i\ge k+1-w_i.
$$

The sum of the three lower bounds is $M+k-e$. Thus $e\ge0$, and the excess of $\sum_i(a_i+X_i)$ over that sum is at most $e$.

Call a row tight if $a_i+X_i=k+1-w_i$, and saturated if $A-a_i=k$. A tight row forces every neighbor of $u$ in $C_i$ to use the full width $w_i$, by equality in the internal-degree count. A saturated row uses the entire even-distance budget of every neighbor of $u$ in $C_i$ on foreign neighbors of $u$. This makes such a vertex adjacent to every other vertex of its component, since otherwise an internal shortest path to a nonneighbor would produce an additional vertex at distance two. It also forces adjacency to every exterior neighbor of $C_i$, since an exterior nonneighbor would be reached at distance two through another vertex of $C_i$.

If a row is both tight and saturated, the component is contained within distance two from $u$, so $|C_i|=a_i+X_i=k+1-w_i$. Every vertex in it is high and must have at least $w_i$ exterior neighbors, hence all are adjacent to $u$. This implies $a_i=|C_i|=k+1-w_i$. But $a_i=A-k\le\lfloor k/2\rfloor$, a contradiction whenever $w_i\le\lceil k/2\rceil$, as holds at the displayed thresholds.

If $e=0$, then $A=M$ and every row is tight. At least one is saturated, since each $a_i\ge M-k=\lfloor k/2\rfloor$ and the sum $M$ exceeds three times this lower bound by at most one. Thus $e=0$ is impossible.

If $e=1$, then $A$ is either $M$ or $M-1$. If $A=M$, at least two rows are saturated, and at least two are tight, a contradiction. If $A=M-1$, then $\sum X_i=k$ and every row is tight. For even $k=2m$, the sum $A=3m-1$ with each $a_i\ge m-1$ ensures a saturated row, since otherwise all three would be at least $m$. Thus $e=1$ is impossible for even $k$. For odd $k$, in the remaining case every row is tight and $\sum X_i=k$.

If $e=2$ and $k=2m$ is even, then $A$ is $M$, $M-1$ or $M-2$. If $A=M$, all three rows are saturated, and at least one is tight, impossible. If $A=M-1$, at least one row is saturated as above. Therefore $\sum X_i=k$ is necessary, since otherwise all rows would be tight. With $\sum X_i=k$ only one unit of excess remains, so every row is either tight or saturated. If $A=M-2$, then $\sum X_i=k$ and all rows are tight.

In each remaining case considered above, $\sum X_i=k$ and the width-two row is tight or saturated. Its chosen neighbor of $u$ is adjacent to both exterior neighbors. The other exterior neighbor is consequently at distance at most two from $u$, and cannot be at distance two because the chosen components already use the entire cap at $u$. Thus the two exterior neighbors of that component are adjacent.

These bounds give the first four rows of the displayed threshold table by substitution of the corresponding maximum reciprocal-bad width sum. For $b\ge6$ and $5k>12(b-1)$, we have $k\ge2b+1$ and hence $\lceil k/2\rceil\ge b+1$. Thus $W\le b+4$ implies $e\le0$, which has just been excluded. This proves the final row.
