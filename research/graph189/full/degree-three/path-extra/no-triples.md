# Path-centered masks 1, 2, 4, 6 with no triple-visible remote

Consider the rooted distance-layer setting for Graph 189. The graph
has order $n>3k$, $k\ge9$, and a degree-three root $z$ of eccentricity
at most three. Every other vertex has degree at least $k$, and every
vertex has at most $k$ vertices at distance exactly two. The three
anchors form a path whose center is anchor 1. The middle layer has
$k$ vertices. Its four exceptional ports $A,B,C,D$ have anchor masks
1, 2, 4, 6 respectively. The remaining $k-4$ middle vertices form
$W$ and see all anchors. Write $F$ for the remote layer,
$c=|F|\ge2k-3$, and $V_i$ for the remotes visible at distance two
to anchor $i$. Assume that no remote belongs to all three visible sets.

**Claim.** This template is impossible.

Write $R_J=N(J)\cap F$ for the remote support of a port $J$, and
$H_J=N_{G[F]}[R_J]$ for its closed remote neighborhood. Put
$a_J=|W\cap N(J)|$. A remote touches some middle vertex and none of
the root or anchors. Since it is not triple-visible, it misses $W$.
It cannot touch both $A$ and $D$ or all of $A,B,C$. It can touch
$A,B$ or $A,C$. Thus every remote has at most three ports and has
closed remote neighborhood of size at least $k-2$. If it has just
one port, this bound becomes $k$.

## Support and boundary bounds

The central anchor already has nonremote distance-two partners
$B,C,D$. Each leaf anchor already has the opposite leaf anchor and
$A$. Thus $|V_1|\le k-3$ and $|V_2|,|V_4|\le k-2$.
By taking complements of the other two visible sets in $F$, there
is at least one $A$-only remote, at least two $B$-only remotes,
and at least two $C$-only remotes. Visibility from one anchor
alone forces the corresponding singleton port as the sole middle
neighbor.

The external remote boundary $H_J\setminus R_J$ lies at distance two
from $J$. So do the $k-4-a_J$ missed members of $W$, via $J$'s
anchor neighbors. Port $A$ additionally sees the root and both leaf
anchors at distance two. Port $B$ additionally sees the root and
central anchor at distance two, and sees either $D$ via leaf anchor 2
(if $BD$ is absent) or leaf anchor 4 via $D$ (if $BD$ is present).
The symmetric argument applies to $C$. Port $D$ sees the root and
central anchor at distance two. These disjoint contributions give

$$
 |H_J|-|R_J|\le a_J+1\quad(J=A,B,C),\qquad
 |H_D|-|R_D|\le a_D+2.
$$

As $H_A,H_B,H_C$ contain the closed neighborhood of a remote with one
port, each has size at least $k$. The visible caps imply $a_A\ge2$,
$a_B,a_C\ge1$, and $|R_A|\ge3$ by using $a_A\le k-4$.
Also $|R_D|\le k-4$, since $R_D\subseteq V_2$ and excludes the two
$B$-only remotes.

## The carrier is a star on all four ports

Any $w\in W$ has three anchor neighbors, at most $k-5$ neighbors
in $W$, and no remote neighbors, so it meets at least two ports.
If it meets exactly three, remotes outside their union of supports
have only the omitted port, and number at most $k-2$ by the visible
caps. Then $w$ sees at least $c-(k-2)\ge k-1$ remotes at distance
two, besides $z$ and the omitted port, impossible. If it meets all
four, every remote is at distance two, also impossible. Hence it meets
exactly two ports, and the two supports have union size at most
$k-3$ since $w$ also sees $z$ and both missed ports at distance two.

The resulting port pairs are pairwise intersecting. Two disjoint
pairs would have support unions covering all of $F$, with total
size at most $2(k-3)<c$. The union of the occurring pairs includes
$A,B,C$ by their incidence lower bounds. It also includes $D$.
If $a_D=0$, then $D$ needs at least one remote neighbor
to reach degree $k$, as it has at most two anchors and three other
ports available. In that event $|H_D|\le k-2$ and every remote
in $R_D$ has closed remote neighborhood of size at least $k-2$
inside $H_D$. Equality is forced, so every member of $R_D$ has
all three leaf ports and $|R_D|=k-4$. Consequently
$|R_B|,|R_C|\ge k-2$ by their two solo remotes each. Then $A$
has no possible partner among $B,C$, a contradiction.

An intersecting family of two-element subsets is a star or contained
in a triangle. To see this, take intersecting pairs $P Q,P R$.
Any pair missing $P$ must be $Q R$, after which every pair is on
those three ports. Since all four ports occur, the family is a star
on all four, centered at a port $P$. Each of its three satellites $J$
has $a_J\le k-6$ because their incidences sum to $k-4$ and each occurs.

## Split at a remote of the star center

We first show that $|H_J|\le2k-8$ for all four ports.

- If $P=A$, its pair with $B$ and the two $B$-only remotes
  give $|R_A|\le k-5$. Since $a_A=k-4$, we get $|H_A|\le2k-8$.
  Each satellite $J$ has $|R_J|\le k-4$ because at least one
  $A$-only remote does not belong to it. Its boundary is at most
  $a_J+2\le k-4$.
- If $P=B$ or $P=C$, its pair with the other singleton leaf port
  and that port's two solo remotes give $|R_P|\le k-5$.
  Its boundary is at most $k-3$. Each satellite $J$ has
  $|R_J|\le k-5$ because the paired center has two solo remotes.
  Its boundary is at most $a_J+2\le k-4$.
- If $P=D$, its pair with $A$ and $|R_A|\ge3$ give
  $|R_D|\le k-6$ by disjointness. The boundary of $R_D$ is at most
  $k-2$. Each satellite support has size at most $k-3$ from its
  pair with $D$, and its boundary is at most $a_J+1\le k-5$.

There is a remote $x\in R_P$. For a singleton center use a solo
remote. If $P=D$ and $R_D$ is empty, degree $k$ would force
$D$ to meet at least two singleton ports in addition to $W$ and
its two anchors. Each singleton support has size at most $k-3$,
so any two attached supports cover at least $c-(k-3)\ge k$ remotes
at distance two from $D$, besides $z$, impossible.

Let $K=N_{G[F]}[x]$, let $\Delta$ be its external remote boundary,
and let $L=F\setminus(K\cup\Delta)$. Each vertex of $\Delta$ is at
distance two from $x$. So are all $k-4$ members of $W$ via $P$ and
at least one anchor. Hence $|\Delta|\le3$. Also $K\subseteq H_P$,
so $|L|\ge(2k-3)-(2k-8)-3=2$.

No support can meet both $K$ and $L$. If $y\in R_J\cap K$
and $y'\in R_J\cap L$, their closed remote neighborhoods lie in
$K\cup\Delta$ and $L\cup\Delta$, respectively, and both lie in
$H_J$. Each neighborhood has size at least $k-2$, so their union
has size at least $2(k-2)-3=2k-7$, exceeding $|H_J|$.

At least two supports meet $L$. Otherwise its vertices have only
one port $J$, and a closed remote neighborhood from $L$ has size
at least $k$ within $L\cup\Delta$. Thus $|L|\ge k-3$.
Port $J\ne P$ since $P$ meets $K$, so their occurring pair
would see all of $L$ and $x$, violating the support-union cap
$k-3$. Therefore $K$ uses at most two supports. It uses $P$,
and is covered by the union of $P$ and at most one satellite.
Either that pair or an arbitrary pair with the center, if there is no
satellite in $K$, contradicts $|K|\ge k-2$ and the pair cap $k-3$.
