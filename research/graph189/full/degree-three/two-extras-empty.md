# Two triangle-anchor templates with no triple-visible remote

In the Graph 189 rooted distance-layer setting, let $k\ge9$, let the
degree-three root $z$ have eccentricity at most three, and assume the
graph has order greater than $3k$. Every vertex except $z$ has degree
at least $k$, and every vertex has at most $k$ vertices at distance
exactly two. Here the anchors form a triangle, the middle layer has
size $k$, and the five exceptional middle ports have one of the
following lists of anchor masks.

- The singleton-plus-two-double template has $A,B,C,D,E$ with masks
  $1,2,4,3,5$ respectively.
- The doubled-singleton-plus-double template has $P,Q,B,C,D$ with
  masks $1,1,2,4,6$ respectively.

The other $k-5$ middle vertices form $W$ and see all three anchors.
Write $F$ for the remote layer, with $c=|F|\ge2k-3$. For anchor $i$
let $V_i$ be its visible remote set. Assume $T=V_1\cap V_2\cap V_4$
is empty. **Both templates are impossible.**

## Common support bounds

For any port $J$ write $R_J=N(J)\cap F$, let $H_J$ be the closed
neighborhood of $R_J$ in $G[F]$, and put $a_J=|W\cap N(J)|$.
A remote has no neighbors among the root, anchors, or $W$. It has at
least one port, and all its port masks together use at most two
anchor labels because $T$ is empty. In either template at most
three ports have masks inside any one two-element anchor set.
Thus every closed remote neighborhood has size at least $k-2$;
with just one port it has size at least $k$, and with at most two
ports it has size at least $k-1$. A solo remote of $J$ has $J$
as its only port.

The distance-two partners of a port include its external remote
boundary $H_J\setminus R_J$, the $k-5-a_J$ members of $W$ missing
it, the root, and each anchor missing that port. The latter anchors
are reached through the anchor triangle. Therefore

$$
 |H_J|-|R_J|\le
 \begin{cases}
 a_J+2,&\text{if }J\text{ is a singleton},\\
 a_J+3,&\text{if }J\text{ is a double}.
 \end{cases}
$$

A port with a solo remote has $|H_J|\ge k$. For each anchor, the
exceptional ports missing that anchor are at distance two from it
via the triangle. This gives caps $(k-2,k-3,k-3)$ for
$(|V_1|,|V_2|,|V_4|)$ in the first template and $(k-3,k-3,k-3)$
in the second. By taking complements of pairs of visible sets,
the first template has at least three $A$-only remotes and at
least two each of $B$-only and $C$-only. The second has at least
three each of $B$-only and $C$-only. Here visibility only at a
singleton anchor with one corresponding port makes the remote
a solo of that port.

## The omitted-pair carrier

A vertex $w\in W$ has three anchor neighbors, at most $k-6$ neighbors
within $W$, and no remote neighbors. It therefore touches at least
three ports. If it touches four, all remotes outside their support
union are supported solely by the missing port, whose support has
at most $k-2$ members. At least $k-1$ remotes would be distance two
from $w$, besides $z$ and the missed port. If it touches five,
all remotes would be distance two. Both contradict the distance-two
cap. It touches exactly three, and their support union has size at
most $k-3$ because $z$ and the two missed ports are also distance
two from $w$.

Call the two missed ports its omitted pair. Their missed remote set
consists of the remotes all of whose supports lie in that pair.
Its size is at least $c-(k-3)\ge k$. In an occurring omitted pair
$\{J,J'\}$, port $J$ has at least $k-|R_{J'}|$ solo remotes
by excluding $R_{J'}$ from this missed set. The two masks in an
omitted pair must be disjoint, since otherwise every missed remote
would belong to one visible set of size at most $k-2$.

Two occurring omitted pairs cannot be disjoint. Their complementary
touched triples would jointly see all remotes, with combined support
size at most $2(k-3)<c$. Thus the occurring pairs are an intersecting
family of two-element sets. They form a star or consist of all
three edges of a triangle. Indeed, two distinct pairs sharing a
port $J$ can be joined by a pair avoiding $J$ only by choosing both
of their other endpoints, and no further pair meets all three.

A port touched by every member of $W$ has nonempty remote support.
If its support were empty, the degree condition would force a singleton
to touch all four other ports. It would see all remotes at distance
two. For a double, the degree condition would force it to touch at
least three other ports. Their supports then cover all but at most
$k-2$ remotes. At least $k-1$ remotes would be distance-two partners,
besides the root and the missed anchor.

## Excluding an omitted triangle

In the first template the allowed omitted pairs are
$AB,AC,BC,BE,CD$, so the only triangle is $AB,AC,BC$.
The two doubles $D,E$ are touched by every $w$, while $A,B,C$
are the three satellites. In the second template, allowed omitted
pairs are $PB,PC,PD,QB,QC,QD,BC$. The omission triangle is $PBC$
or $QBC$. Relabel the twins so it is $PBC$. Then $Q,D$ are touched
by every $w$, with satellites $P,B,C$.

In both cases every satellite $J$ has at least three solos. For the
first template, the omission $BC$ gives three each for $B,C$,
and either omission involving $A$ gives three for $A$.
In the second template all three follow from the uniform visible
cap $k-3$. Also each satellite has $a_J\le k-7$, because each $w$
touches exactly one satellite and all three satellite classes occur.
It has $|R_J|\le k-3$ because it is touched by some $w$. Hence
each satellite has $|H_J|\le2k-8$.

In the first template the universal doubles $D,E$ have support
size at most $k-6$, using respectively $V_2$ minus the three
$B$-solos and $V_4$ minus the three $C$-solos. Thus their boundary
cap $a_J+3=k-2$ gives $|H_J|\le2k-8$. In the second template the
universal double $D$ similarly has $|R_D|\le k-6$ using $V_2$.
The universal singleton $Q$ has $|R_Q|\le k-6$ using $V_1$
minus the three $P$-solos. In particular both universal ports
again obey $|H_J|\le2k-8$.

Choose $x\in R_D$, which exists since $D$ is universal to $W$.
Split $F$ into $K=N_{G[F]}[x]$, its external remote boundary
$\Delta$, and $L=F\setminus(K\cup\Delta)$. As $x$ sees all $W$ and
the two anchors of $D$ at distance two, $|\Delta|\le3$.
Since $K\subseteq H_D$, we get $|L|\ge2$. A port cannot have
support in both $K$ and $L$. Two such support points have their
closed remote neighborhoods in $K\cup\Delta$ and $L\cup\Delta$,
respectively. Both neighborhoods lie in $H_J$ and each has size
at least $k-2$, so their union would have size at least $2k-7$.

If $L$ used just one port $J$, its remote neighborhoods would
give $|L|\ge k-3$. Some $w$ touches $J$ and $D$ (every port occurs
in a touched triple and $D$ is universal), so it would see $L$
and $x$ at distance two in excess of the support cap $k-3$.
Thus $L$ uses at least two ports and $K$ uses at most three.
The ports used by $K$ meet every omitted pair, because otherwise
the complementary triple would see all of $K$, of size at least
$k-2$. As $D$ is in $K$ and is not an omitted port, $K$ uses
exactly $D$ and two of the three satellites. Thus $L$ uses the
other universal port and the remaining satellite $J$.

Some $w$ touches both of the latter ports and $D$, so
$|L|+1\le k-3$. If a remote of $L$ were solo, its closed
remote neighborhood of size at least $k$ inside $L\cup\Delta$
would contradict this bound. Thus every remote in $L$ touches
both ports and has closed neighborhood of size at least $k-1$.
Together with $|\Delta|\le3$ and $|L|\le k-4$ this forces
$|\Delta|=3$ and $|L|=k-4$. The at least three solos of $J$
belong to $\Delta$ because $R_J$ avoids $K$ and every $L$ point
has two ports. Therefore $|R_J|\ge |L|+3=k-1$, exceeding its
visible cap. This excludes every omitted triangle in either template.

## Excluding an omitted star

A common endpoint of the omitted star is missed by every $w$,
so it has $a_J=0$ and a solo by the omitted-pair bound; hence
$|H_J|\ge k$. In the second template all singleton ports have
$|R_J|\le k-3$, giving $|H_J|\le k-1$ if $a_J=0$.
Its double has $|R_D|\le k-6$ by excluding the three $B$-solos
from $V_2$, giving $|H_D|\le k-3$ if $a_D=0$. No port can be
the star center.

In the first template, singleton ports $B,C$ have $|R_J|\le k-3$;
the doubles have $|R_D|,|R_E|\le k-5$ by excluding the two
$B$-solos and two $C$-solos from $V_2$ and $V_4$, respectively.
None of these four ports can have $a_J=0$, since such a port is
in an omitted pair, has a solo, and $|H_J|<k$ by the boundary cap.
Hence the center is $A$. Its only allowed omissions are $AB,AC$,
and both occur, because just one would isolate the other member
of that pair as well. The degree-two boundary allowance and the
solo support force $|R_A|=|V_1|=k-2$ and $|H_A|=k$. Thus
$R_D,R_E\subseteq R_A$. Both doubles are universal to $W$
and have nonempty support.

Split at $x\in R_D$ just as above. Then $|\Delta|\le3$,
$K\subseteq H_A$ and $|L|\ge k-6>0$. The same two-neighborhood
argument shows $R_A$ cannot cross $K,L$, since $k<2k-7$.
Therefore $R_A,R_D,R_E$ all avoid $L$. The only two satellite
classes in $W$ are $B,C$ and both occur, so $a_B,a_C\le k-6$.
The masks of $B$ and $E$ jointly see all anchors, so their
supports are disjoint. Similarly $R_C$ and $R_D$ are disjoint.
A $w$ touching $B$ also touches $E$, and a $w$ touching $C$
also touches $D$. Nonempty $R_E,R_D$ and the support cap give
$|R_B|,|R_C|\le k-4$, and thus $|H_B|,|H_C|\le2k-8$.
Neither $R_B$ nor $R_C$ can cross $K,L$.

At least one of $B,C$ supports some point in $K$, because otherwise
$K\subseteq R_A$ and $x$ could touch only $A,D,E$. It cannot
touch both doubles without becoming triple-visible, so it would
have at most two ports, giving $|K|\ge k-1>|R_A|$. Hence $L$
uses only the other singleton port. A solo $L$ point has closed
remote neighborhood of size at least $k$, so $|L|\ge k-3$.
A $w$ touching that singleton and the universal $D$ sees all of
$L$ and also $x$, exceeding the support cap. This excludes the
final star carrier.
