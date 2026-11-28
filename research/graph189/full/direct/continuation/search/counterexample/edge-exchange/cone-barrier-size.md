# A cone without a 2-factor needs a large canonical barrier

Let $G$ satisfy Graph 189 with $k\ge11$ and connectivity at least five. Adjoin a universal vertex $z$ to form the cone $G^+$. If $G^+$ has no 2-factor, then every biased Tutte barrier of $G^+$ has $z$ in its first set and at least $k+1$ other vertices there. This gives a restriction on factor certificates of nontraceability, since a spanning path of $G$ would extend to a spanning cycle of its cone.

We use Tutte's 2-factor theorem and the standard biased-barrier lemma. A biased barrier minimizes $|T|$ and then maximizes $|S|$ among pairs with negative even deficiency
$$
\delta(S,T)=2|S|-2|T|+\sum_{t\in T}d_{G^+-S}(t)-q,
$$
where $q$ counts the odd components of $G^+-(S\cup T)$, whose number of edges to $T$ is odd. In a biased barrier, $T$ is independent, even components do not touch $T$, each $T$ vertex meets any component in at most one neighbor, and each component vertex has at most one $T$ neighbor. These are the properties proved in [Kanno and Shan, Lemma 3.2](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v26i2p17/7831). We also use the established order bound $n\le1+2k+\lfloor(k+1)^2/4\rfloor$.

If $z\in T$, then $T=\{z\}$ and all exterior components are singletons by the canonical incidence property. The deficiency equals $2|S|-2$ so it can be negative only on an edgeless $G$, impossible. Suppose $z$ is exterior. There is one exterior component and every $T$ vertex has precisely one neighbor there, namely $z$. The negative deficiency gives $|T|-1\ge2|S|$, and each $T$ vertex has all its $G$ neighbors in $S$. Each anchor has at most $k+1$ contacts in $T$, since they are independent and any one of its contacts sees the others at distance two. Thus $(|T|-1)k\le|S|(k+1)$, contrary to $k>1$ and $|S|\ge1$.

It follows that $z\in S$. From now on remove $z$ from $S$, and put $s=|S|$, $t=|T|$, and $U=V(G)\setminus(S\cup T)$. Let $E$ be the number of edges from $T$ to $U$. The odd-component count is unchanged. The deficiency falls by two, so
$$
t\ge s+2,\qquad q\ge E-2(t-s-2).
$$
Each matched $U$ neighbor of a given $T$ vertex is in a distinct component. All but at most one $T$ vertex are high and have only high neighbors in $U$. Call these good. If the low vertex is in $T$ it is the sole exception, and if it lies in $U$ it has at most one $T$ neighbor. A good vertex $v$ has $b_v$ neighbors in $U$ and at least $k-b_v$ neighbors in $S$. Any of its neighbors $x$ in an exterior component $D$ supplies $d_D(x)$ exact distance-two witnesses. These are distinct across its contacts, and $d_D(x)+|N(x)\cap S|\ge k-1$.

If $r=k-s\ge3$, then $b_v\ge r$ and every $d_D(x)\ge r-1$. Consequently $b_v\le k/(r-1)$, so every good $T$ vertex has at least $k-k/(r-1)>s/2$ anchor neighbors. All good $T$ pairs are at distance two through a shared anchor. A good vertex therefore sees at least $t-2\ge s$ other good $T$ vertices plus at least $r(r-1)$ internal exterior witnesses. This exceeds $k=s+r$.

For the next three cases write $k=2d$ or $2d+1$. Call a good $T$ vertex dense if it has more than $s/2$ anchor neighbors, and write $h$ for their number. Dense pairs are at distance two.

## The case $s=k-2$

Every good vertex has $b_v\ge2$, and each contact supplies at least one internal witness. Every contact $x$ of a dense vertex then has $d_D(x)\le k-h$, after counting the other $h-1$ dense vertices and at least one other internal witness. If $h\ge\lceil k/2\rceil$, this is at most $\lfloor k/2\rfloor$. Each dense vertex has at least $\lfloor k/2\rfloor$ anchor neighbors, so its anchor set meets that of $x$, because $|N(x)\cap S|\ge k-1-d_D(x)$. Thus each dense vertex sees the $h-1$ other dense vertices as well as all their at least $2(h-1)$ distinct $U$ contacts. This is more than $k$. In particular $h\le\lceil k/2\rceil$.

Each good nondense vertex needs $b_v\ge\lceil k/2\rceil+1$ contacts. Hence
$$
q\ge E-2(t-k)
\ge(t-h-1)(\lceil k/2\rceil-1)+2k-2
\ge \lfloor k^2/4\rfloor+k-1.
$$
The order is at least $s+t+q\ge\lfloor k^2/4\rfloor+3k-3$, above the quadratic upper bound for $k\ge11$.

## The case $s=k-1$

Every good vertex has $b_v\ge1$, and any contact of a dense vertex has $d_D(x)\le k-h+1$. If $h\ge d+2$, this bound is smaller than every dense anchor support. Since $|N(x)\cap S|\ge k-1-d_D(x)$, the support of each such $x$ intersects every dense support. Each dense root then sees at least $2(h-1)>k$ witnesses from the other dense vertices and one of their respective $U$ contacts. Thus $h\le d+1$.

The good nondense vertices require $b_v\ge d+1$. Therefore
$$
q\ge (d-1)(t-h-1)+2k-h\ge\lfloor(k+1)^2/4\rfloor.
$$
The last value is attained when $t=k+1$ and $h=d+1$. The bound $n\ge s+t+q$ then leaves at most one extra vertex under the known order ceiling. Increasing $t$ or decreasing $h$ costs at least $d$ in that bound. Thus the displayed choices of $t,h$ are forced. With $t=k+1$ the deficiency gives $q\ge E$, and the minimum sum of $U$ incidences over the good vertices is $\lfloor(k+1)^2/4\rfloor$. There is at most one excess incidence, so any dense vertex has $b_v\le2$.

There are at least $q-2$ high singleton odd components. Indeed $|U|\le q+1$ leaves at most one nonsingleton odd component and at most one low vertex. Each high singleton has one $T$ neighbor and must see every anchor, since otherwise its degree is below $s+1=k$. A dense root then sees all but its at most two direct contacts among these high singletons at distance two. Thus it sees at least $q-4>k$, a contradiction.

## The case $s=k$

First suppose every good vertex has $b_v\ge1$. As before, for a contact of a dense root, $d_D(x)\le k-h+1$. If $h\ge d+2$ at even $k$ or $h\ge d+3$ at odd $k$, every dense support has size at least $d+1$ and the bound gives $d_D(x)\le d-1$. Thus $N(x)\cap S$ meets every dense support, using $|N(x)\cap S|\ge k-1-d_D(x)$. A dense root sees at least $2(h-1)>k$ witnesses. Therefore $h\le d+1$ at even $k$ and $h\le d+2$ at odd $k$.

A good nondense vertex requires $b_v\ge\lceil k/2\rceil$. Consequently
$$
q\ge(\lceil k/2\rceil-2)(t-h-1)+2k+2-h.
$$
With $t\ge k+2$, this gives $q\ge d^2+d+1$ at even $k$ and $q\ge d^2+2d+2$ at odd $k$. In either parity $n\ge s+t+q$ is at least two above the order ceiling.

Finally, if a good vertex $v_0$ has $b_{v_0}=0$, it is adjacent to every anchor. Let $a$ count $T$ vertices with a nonempty anchor support, let $w=t-a$, and let $p$ count the vertices of $U$ with an anchor neighbor. The even quota at $v_0$ gives $a-1+p\le k$. Since $t\ge k+2$, at least one $T$ vertex has no anchor neighbor. If all such vertices are low, there is exactly one, $a=k+1$, $t=k+2$ and $p=0$. Then the deficiency gives $q=E$, so each odd component has just one $T$ attachment. The low, having positive degree, meets such a component. That component has no anchor contacts and only one $T$ attachment, contrary to connectivity.

Otherwise a high $T$ vertex with no anchor contacts needs at least $k$ distinct exterior components, giving $q\ge k$. Each odd component missing all $p$ exterior anchor contacts has at least five boundary vertices, all in $T$. Thus $(E-q)/2\ge2(q-p)$. By the deficiency and the budget at $v_0$,
$$
t\ge k+2+2(q-p)\ge k+2a,
\qquad w\ge k+a.
$$
At most one of those $w$ vertices is low, hence $E\ge k(w-1)$. Therefore
$$
n\ge k+t+q\ge k+t+E-2(t-k-2)
\ge 2k+4-a+(k-1)w\ge k^2+k+4,
$$
again impossible. All cases $s\le k$ are now excluded.
