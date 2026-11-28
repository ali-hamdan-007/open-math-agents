# Internal degree bounds for separators in Graph 189

Let $G$ be a finite simple 2-connected graph, and let $k$ be its second-smallest degree. Suppose every vertex has at most $k$ other vertices at even distance. If $S$ is inclusion-minimal with $c(G-S)\ge |S|+2$, then

$$
\Delta(G[S])\ge \left\lceil \frac{k}{4}\right\rceil .
$$

Consequently $c(G-S)\le |S|+1$ whenever $\Delta(G[S])<k/4$. This includes every independent separator. Passing to an inclusion-minimal violating subset can only decrease $\Delta$.

## Incidence bounds for a minimal separator

Write $s=|S|$, $c=c(G-S)$ and $C_1,\ldots,C_c$ for the components of $G-S$. By 2-connectivity, $s\ge2$. If $T\subsetneq S$, at most $|T|$ components of $G-S$ have all their neighbors in $T$. Each such component is still a component of $G-T$, and at least one more component contains a vertex of $S\setminus T$. Minimality gives $c(G-T)\le |T|+1$.

Take an outside vertex $x\in C_i$ with $Q=N(x)\cap S\ne\varnothing$ and put $q=|Q|$. At least $c-(s-q)-1\ge q+1$ other components meet $Q$, each supplying a distance-two vertex from $x$. It follows that $q\le k-1$. A singleton component must therefore have degree below $k$, and there is at most one such vertex in $G$. Every nonsingleton component contains at least two vertices adjacent to $S$, since a unique such vertex would be a cut vertex. Also, the neighbors of any component in $S$ are at least two in number, since a unique neighbor in $S$ would be a cut vertex.

Every $u\in S$ has neighbors in at least three components. If it meets $t$ components, adding it back leaves $c+1-t$ components. Minimality gives $c+1-t\le s$, so $t\ge c+1-s\ge3$.

## Choosing a separator vertex

There exists a vertex $u\in S$ of degree at least $k$ with a neighbor of degree at least $k$ in every component it meets. If the possible vertex $z$ of degree below $k$ is in $S$, choose any other separator vertex. If no $z$ exists, choose any separator vertex. If $z$ lies in a nonsingleton component of $G-S$, that component has at least one other vertex adjacent to $S$, and choosing one of that vertex's neighbors in $S$ works. If $z$ is a singleton and misses a separator vertex, that separator vertex works.

It remains to exclude a singleton component $z$ adjacent to all of $S$. In this case $k>s=\deg(z)$. Let $h=k-s$, and let $B$ consist of all vertices outside $S$ adjacent to $S$. The vertex $z$ is at distance two from all of $B\setminus\{z\}$, so

$$
2(c-1)\le |B|-1\le k,
\qquad h\ge s+2.
$$

Fix $u\in S$ and write $d=\deg_{G[S]}(u)$. Since $\deg_G(u)\ge k$ and $|B|\le k+1$, the vertex $u$ misses at most $d+1$ vertices of $B$. It meets at least $r=s+1-m$ components other than $z$, where $m=\lfloor(d+1)/2\rfloor$: of the at least $s+1$ such components, every component missed by $u$ contains at least two vertices of $B$.

In each component other than $z$ that meets $u$, a neighbor $x$ of $u$ has at least $k-s=h$ neighbors inside that component. The vertex $x$ and its internal neighbors all lie in the first two distance layers from $u$. Across these components, the first layer has size at most $|B|-1\le k$. The second layer has size at most $k-(s-1-d)=h+1+d$, since the $s-1-d$ separator nonneighbors of $u$ are also at distance two via $z$. Consequently

$$
(s+1-m)(h+1)\le k+h+1+d,
\qquad
(s-1-m)h\le d+m.
$$

For $s\ge3$, this is impossible. We have $m\le\lfloor s/2\rfloor$, $d\le s-1$ and $h\ge s+2$, but

$$
\left(s-1-\left\lfloor\frac{s}{2}\right\rfloor\right)(s+2)
  >s-1+\left\lfloor\frac{s}{2}\right\rfloor .
$$

For $s=3$ the two sides are $5$ and $3$. For $s\ge4$, moving the terms involving $\lfloor s/2\rfloor$ to the right gives $s^2-1>\lfloor s/2\rfloor(s+3)$, which follows from $s^2-3s-2>0$. When $s=2$, every component meets both separator vertices by 2-connectivity, so the first bound improves to $3(h+1)\le k+h+1+d\le2h+4$. This conflicts with $h\ge s+2=4$. The proposed singleton is therefore impossible.

## Counting from the chosen separator vertex

Choose $u$ as above and number the components it meets from $1$ to $t$. Put

$$
a_i=|N(u)\cap C_i|,\qquad A=\sum_{i=1}^t a_i,\qquad
X_i=|\{x\in C_i:d(u,x)=2\}|,\qquad X=\sum_{i=1}^t X_i .
$$

For each $i$, choose a neighbor $x_i\in C_i$ of $u$ with $\deg_G(x_i)\ge k$, and put $q_i=|N(x_i)\cap S|$. The vertex $x_i$ and its at least $k-q_i$ internal neighbors lie in the first two distance layers from $u$, so $a_i+X_i\ge k+1-q_i$.

The representatives at distance two from $x_i$ can be chosen among the neighbors of $u$ in all other components that meet $u$, since $u\in N(x_i)\cap S$. The remaining neighbors of $u$ in those components are also at distance two from $x_i$, so

$$
q_i+1+\sum_{j\ne i}(a_j-1)\le k.
$$

Combining and summing over $i$ gives

$$
X\ge t+(t-2)(A-t)\ge A,
$$

where $t\ge3$ and $A\ge t$.

Let $d=\deg_{G[S]}(u)$ and let $\ell$ count the separator vertices at distance two from $u$. The degree lower bound gives $A+d\ge k$. The even-distance cap gives $X+\ell\le k$. Since $X\ge A$, these two inequalities imply $\ell\le d$ and $A+X\le2(k-\ell)$. Every neighbor of $x_i$ in $S$ is either $u$, a separator neighbor of $u$ or a separator vertex at distance two from $u$. Thus $q_i\le 1+d+\ell$, and summing $a_i+X_i\ge k+1-q_i$ yields

$$
t(k-d-\ell)\le A+X\le2(k-\ell).
$$

Therefore

$$
k\le \ell+\frac{t}{t-2}d\le 4d.
$$

In particular the chosen separator vertex has internal degree at least $\lceil k/4\rceil$, with the sharper bound $k\le3d$ whenever it meets at least four components.
