# A common even cover for the private and singleton cases

Write $X,Y$ for the high vertices on the two sides $A,B$ of a minimum
separator $S$. Let $C$ be the labels adjacent to all of $X$. Suppose
each member of $X$ touches at most one label in $D=S\setminus C$, and
each label in $D$ has a representative $x_i\in X$ touching it. Write
$s=|S|, c=|C|, d=|D|>0$. The support of $x_i$ is exactly $C\cup\{i\}$.

Use the even-distance neighborhoods of the $c$ common labels and the
$d$ representatives to cover $Y$. The common labels each cover at most
$k$ vertices. Each representative covers at most $k-d+1$, by the
boundary debit at this minimum separator. Every opposite port is covered,
because its separator neighbor is adjacent to at least one representative.
An uncovered $y\in Y$ is therefore a nonport at odd distance from every
representative. The high-pair distance bound makes each of these distances
three. The geodesic from $x_i$ to $y$ goes first to a separator label
at distance two from $y$. Every common label seeing $y$ at distance
two would cover it. Hence $y$ is at distance two from **every** $i\in D$.

Let $H_i=\{x\in X:x\sim i\}$. At most $|H_i|+c+1$ members of $Y$
are at distance two from $i$. Indeed, the closed internal neighborhood
of $x_i$ has at least $k+1-(c+1)$ vertices. Deleting the possible low
vertex and the members of $H_i$ leaves vertices at distance two from
$i$, on the $A$ side. They consume the same quota. As the $H_i$
are pairwise disjoint, summing the cover bound for each choice of $i$
gives

```
d |Y| + d²(d−1) ≤ d(sk+c+1) + |X|.
```

This is the private-support comparison in `Graph189ValidBand.consequences`
when $c=0$. For $c=1,2$, any opposite contact on a common label sees
all of $X$ at distance two, so $|X|\le k$. The two remaining
comparisons in that theorem then exclude both cases.

## Forcing a high private witness

Suppose $c\ge3$, $d\ge2$, and no common label has a high private
contact in $B$. Remove from $Y$ the even neighborhoods of the $d$
representatives alone, covering at most $dk$ vertices. Every remaining
vertex $y$ is a nonport. For each $i\in D$, its distance-two labels
meet $C\cup\{i\}$.

If $y$ has just one distance-two label $j$, then $j\in C$, since
$d\ge2$. The middle vertex of a two-edge geodesic from $j$ to $y$
belongs to $B$ and touches exactly $j$. It must be the unique low
vertex. Therefore only one common label can appear as such a singleton
across all these $y$. Counting that label twice, all remaining vertices
cost at least two distance-two incidences. The common labels have at most
$ck$ incidences, their exceptional duplicate has at most $k$, and
the residual labels together have at most $|X|+d(c+1)$.

Thus $2|Y|\le 2dk+ck+2k+d(c+1)$. Since $c+1\le6(c-2)$ and
$6d<k$ in every valid band, this gives $|Y|\le sk$, contrary to the
large-population bound. Classification reduces every case without a full
high representative to this argument. In the co-singleton alternative
there are at most two residual labels, and any vertex missing one of them
has at most one residual contact.
