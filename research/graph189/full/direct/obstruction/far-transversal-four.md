# Four distant vertices across a large violating separator in Graph 189

Let $G$ be a finite simple 2-connected graph with second-smallest degree $k$ satisfying the Graph 189 even-distance bound. If $S$ is an inclusion-minimal set with $c(G-S)\ge |S|+2$ and $|S|\ge9$, then four vertices of degree at least $k$ in distinct components of $G-S$ are pairwise at distance at least three. In particular $|V(G)|\ge4k+4$. More generally, if $|V(G)|\le4k+3$ and $k\ge16$, then $c(G-S)\le |S|+1$ for every $S$.

Write $s=|S|\ge5$ by the [size-four result](four-vertex-separators.md). Choose $r=s+1$ components consisting entirely of vertices of degree at least $k$. The [port defect bound](depth-and-port-defect.md) implies that every such vertex has at least two neighbors within its component. Each chosen component therefore has size at least $m=\max(3,k+1-s)$, where the second term also follows from the degree bound.

As in the [three-vertex theorem](far-transversal-triple.md), choose $w_i$ vertices in component $i$, allowing $w_i=0$, and let $M=\sum_i w_i$. Form a graph joining pairs of chosen vertices from different components at distance at least three. If it contains no $K_4$, Turán's theorem bounds its edge count by $M^2/3$. Its vertices in component $i$ have at least $M-w_i-k$ neighbors, so

$$
M^2-3\sum_i w_i^2\le3kM.
$$

Uniformly choosing $w_i=m$ gives $(s-2)m\le3k$, and hence $k\ge s-2$. When $s>5$ and $k=s+h>s$, the inequality also gives $(s-5)h\le2s+2$, using $m\ge h+1$.

Call a component small if it has order at most $k-\lfloor s/2\rfloor$. Vertices in distinct small components are pairwise at distance two, because each has more than half of $S$ as neighbors. If there are $L$ remaining components, this gives $L\ge s-\lfloor k/m\rfloor$. Each of these $L$ components has order at least $p=k-\lfloor s/2\rfloor+1$. Applying the Turán bound to $p$ vertices chosen from each of them gives $(L-3)p\le3k$, automatically true when $L\le2$.

For $s\ge18$, the inequality $(s-5)h\le2s+2$ excludes $h\ge3$, so $s-2\le k\le s+2$ and $m=3$. Then $L\ge s-\lfloor(s+2)/3\rfloor\ge12$ and $p\ge k/2$, contradicting $(L-3)p\le3k$.

For $5\le s\le17$, choose $w_i=m$ in the small components and $w_i=p$ in the others. Also the [strict internal degree bound](independent-separators.md) gives $k<4(s-1)$. The following integer calculation checks every remaining parameter.

```python
for s in range(5, 18):
    surviving_k = set()
    upper_k = 4 * (s - 1) - 1
    if s > 5:
        upper_k = min(upper_k, s + (2 * s + 2) // (s - 5))
    for k in range(s - 2, upper_k + 1):
        m = max(3, k + 1 - s)
        if (s - 2) * m > 3 * k:
            continue
        p = k - s // 2 + 1
        for L in range(max(0, s - k // m), s + 2):
            if (L - 3) * p > 3 * k:
                continue
            a = s + 1 - L
            total = a * m + L * p
            if total**2 - 3 * (a * m**2 + L * p**2) <= 3 * k * total:
                surviving_k.add(k)
    print(s, sorted(surviving_k))
```

| $s$ | Surviving values of $k$ without a distant four |
| --- | --- |
| 5 | $3,\ldots,15$ |
| 6 | $4,\ldots,12$ |
| 7 | $5,\ldots,9$ |
| 8 | $6,9,10$ |
| 9–17 | None |

Thus a violating separator of size at least nine has four distant vertices in different components. Their closed neighborhoods are disjoint and each has at least $k+1$ vertices, giving the order lower bound. The table also shows that every minimal violating separator has such a four whenever $k\ge16$, proving the stated conclusion for order at most $4k+3$.
