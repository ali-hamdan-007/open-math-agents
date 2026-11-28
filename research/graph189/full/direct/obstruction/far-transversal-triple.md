# Three distant vertices across a violating separator in Graph 189

Let $G$ be a finite simple 2-connected graph with second-smallest degree $k$. Suppose every vertex has at most $k$ other vertices at even distance. If $S$ is an inclusion-minimal set with $c(G-S)\ge |S|+2$, then there are three vertices of degree at least $k$ in three different components of $G-S$, pairwise at distance at least three.

Write $s=|S|$. The [small-separator bound](four-vertex-separators.md) gives $s\ge5$. At most one vertex has degree below $k$, so choose $r=s+1$ components all of whose vertices have degree at least $k$. Each chosen component has order at least

$$
m=\max(2,k+1-s).
$$

Indeed, the degree bound gives the second term, and the [minimal-separator incidence bound](independent-separators.md) excludes any singleton of degree at least $k$.

## A triangle-free graph of distant pairs

Suppose no such triple exists. Choose $w_i$ vertices in component $i$ for each $i$, allowing $w_i=0$, and let $M=\sum_i w_i$. On these chosen vertices, join each pair from different components at distance at least three in $G$. This graph is triangle-free. Every pair from different components is either such an edge or at distance two in $G$. A chosen vertex in component $i$ has at least $M-w_i-k$ neighbors in the triangle-free graph. Counting degrees and applying Mantel's theorem gives

$$
M^2-\sum_i w_i^2-kM\le 2|E|\le \frac{M^2}{2},
$$

or equivalently

$$
M^2-2\sum_i w_i^2\le 2kM.
$$

Taking $w_i=m$ in all $r=s+1$ components gives $(s-1)m\le2k$, hence $k\ge s-1$. If $k=s+h$ with $h\ge1$, it also gives $(s-3)h\le s+1$. In particular,

$$
s-1\le k\le s+\left\lfloor\frac{s+1}{s-3}\right\rfloor.
$$

Call a chosen component small if its order is at most $k-\lfloor s/2\rfloor$. Each vertex of such a component has at least $\lfloor s/2\rfloor+1$ neighbors in $S$, so vertices in different small components have a common neighbor in $S$ and are at distance two. If there are $s+1-L$ small components, the even-distance cap applied to any vertex in one of them gives $(s-L)m\le k$. The same inequality is automatic if there are no small components. Thus $L\ge s-\lfloor k/m\rfloor$.

Each of the $L$ remaining components has order at least $p=k-\lfloor s/2\rfloor+1$. Taking $w_i=p$ in each of them and $w_i=0$ elsewhere gives $(L-2)p\le2k$. This inequality is automatic when $L\le1$.

For $s\ge8$, the first bounds imply $s-1\le k\le s+1$ and $m=2$. Then

$$
L\ge s-\left\lfloor\frac k2\right\rfloor\ge\left\lfloor\frac s2\right\rfloor,
\qquad
p\ge\frac{k+1}{2}.
$$

Since $(L-2)p\le2k$, we must have $L\le5$, so $s\le11$.

## Exact arithmetic for the remaining sizes

For $5\le s\le11$, take $w_i=m$ in the small components and $w_i=p$ in the others. Writing $a=s+1-L$, the remaining necessary inequality is

$$
(am+Lp)^2-2(am^2+Lp^2)\le2k(am+Lp).
$$

The following integer calculation checks the displayed conditions using the full derived ranges.

```python
for s in range(5, 12):
    survivors = []
    upper_k = s + (s + 1) // (s - 3)
    for k in range(s - 1, upper_k + 1):
        m = max(2, k + 1 - s)
        p = k - s // 2 + 1
        for L in range(s - k // m, s + 2):
            if (L - 2) * p > 2 * k:
                continue
            a = s + 1 - L
            total = a * m + L * p
            if total**2 - 2 * (a * m**2 + L * p**2) <= 2 * k * total:
                survivors.append((k, L))
    print(s, survivors)
```

The only surviving triple $(s,k,L)$ is $(5,6,2)$. There are four small components, each of order at least two. Since every vertex in a small component sees every vertex in the other small components at distance two, all four small components have order exactly two. Each of their vertices has degree at least six, hence is adjacent to all five vertices of $S$. Such a vertex sees all six vertices in the other small components at distance two, as well as any boundary vertex of either remaining component. This exceeds $k=6$, a contradiction.
