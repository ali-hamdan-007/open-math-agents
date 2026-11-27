# All six exceptional masks with no triple-visible remote

Use the Graph 189 rooted setting of the five-port argument, with
triangular anchors and six exceptional middle ports $A,B,C,D,E,F$
of masks $1,2,4,3,5,6$. The common middle vertices form $W$ of
size $k-6$. Write $\mathcal R$ for the remote layer of size
$c\ge2k-3$ and assume no remote is visible from all three anchors.
This note uses only the degree lower bounds and the distance-two
cap, with $k\ge9$. The omitted triangle and the one-edge and
three-edge omitted stars are impossible. The two-edge star reduces
to the specific configuration at the end.

## Support counts and the omitted carrier

Write $R_J$ for a port's remote support, $H_J$ for its closed
remote neighborhood, and $a_J$ for its number of neighbors in $W$.
Every remote has at least one port and at most three, since its
masks are contained in one pair of anchors. Its closed remote
neighborhood has size at least $k-2$, at least $k-1$ if it uses
at most two ports, and at least $k$ if it has exactly one port.
Call this last type solo. Each anchor has three missed ports at
distance two via the triangle, so its visible remote set has
size at most $k-3$. Complementing two visible sets gives at least
three solo remotes for each singleton port. A double has support
size at most $k-6$ because the visible set of either anchor in
its mask also contains three solos of that anchor's singleton.
Distinct doubles have disjoint supports because their masks
together use all three anchors.

Every $w\in W$ meets at least four ports by degree. If it met five,
all but at most $k-3$ remotes would be at distance two, besides
$z$. If it met six, all remotes would be at distance two. It
therefore meets exactly four, with support union of size at most
$k-3$, counting $z$ and both omitted ports separately. The
omitted pair has at least $k$ missed remotes supported only by
that pair. Its masks must be disjoint because otherwise these
remotes would all belong to one visible set. Each endpoint has
at least three solo remotes since the support of the other has
at most $k-3$ vertices. Two omitted pairs cannot be disjoint,
since their complementary four-port unions would cover all
remotes with combined size at most $2(k-3)$. Thus the omission
family is a star or all three edges of a triangle. The possible
edges are $AB,AC,BC,AF,BE,CD$.

The missed members of $W$, the root, and the missed anchors
are at distance two from a port, alongside its external remote
boundary. Hence

$$
|H_J|-|R_J|\le a_J+3\quad\text{for singletons},\qquad
|H_J|-|R_J|\le a_J+4\quad\text{for doubles}.
$$

A port touched by every $w$ has nonempty support. An empty
support would force a singleton to touch all five other ports,
putting all remotes at distance two. A double would have to touch
at least four other ports, putting at least $c-(k-3)\ge k$
remotes and the root at distance two.

For a remote $x$, write $K$ for its closed remote neighborhood,
$\Delta$ for the external remote boundary of $K$, and $L$ for
the remaining remotes. Every member of $\Delta$ is at distance
two from $x$. If a port has support in both $K$ and $L$, two
of its support points have closed remote neighborhoods
contained respectively in $K\cup\Delta$ and $L\cup\Delta$.
Both lie in $H_J$, so $|H_J|\ge 2(k-2)-|\Delta|$.

## Omitted triangle

The only omission triangle is $AB,AC,BC$. All three doubles
are universal to $W$, and each $w$ meets one singleton. Three
pairwise disjoint nonempty double supports together with three
solos of the touched singleton fit in the support cap $k-3$.
Thus each double has $|R_J|\le k-8$ and $|H_J|\le2k-10$.
Each singleton has support at most $k-4$ because it is touched
with the nonempty disjoint support of its opposite double.
The three singleton classes all occur, so $a_J\le k-8$ and
$|H_J|\le2k-9$ for singletons.

Split at $x\in R_P$ for a double $P$. It sees all $W$ and its
two anchors at distance two, hence $|\Delta|\le4$. Also
$K\subseteq H_P$, so $L$ is nonempty. No support crosses $K,L$,
as this would require $|H_J|\ge2k-8$. The ports supporting $K$
must meet every omitted pair, since otherwise the corresponding
touched quartet would see all of $K$, of size at least $k-2$.
Thus at least two singleton supports meet $K$, leaving at most
one singleton on $L$.

If $L$ used no singleton, all its points would be solo by double
support disjointness. Then $|L|\ge k-4$, and every $w$ would see
$L$, $x$, and the solos of its selected singleton, impossible.
Let $J$ be the only singleton used on $L$. Every $L$ point has
at most two ports, and a $w$ touching $J$ sees all $L$ and the
whole support $R_P$ outside $L$. Hence $|L|\le k-3-|R_P|$.

If $|R_P|\ge2$, then $|L|\le k-5$ and $|\Delta|\le4$. The closed
remote degree bound $k-1$ forces $|L|=k-5$ and two ports per point
in $L$. If $|R_P|=1$, the degree of $P$ forces adjacency to at
least three other ports besides $W$, its two anchors, and $x$.
At most two of those ports touch $x$, so another distance-two
partner forces $|\Delta|\le3$. Then $|L|\le k-4$ forces
$|L|=k-4$ and two ports per point in $L$. In either case all $L$
points touch $J$, and its three solos lie in $\Delta$, since
$R_J$ avoids $K$. Consequently $|R_J|>k-3$, impossible.

## Omitted star

A common endpoint of the omitted pairs has $a_J=0$ and solo
remotes, hence $|H_J|\ge k$. A double with $a_J=0$ would have
$|H_J|\le(k-6)+4$. Thus the endpoint is a singleton, say $A$.
It saturates $|R_A|=|V_1|=k-3$ and $|H_A|=k$.

If there is just one omission, its other member cannot be a
double by the same argument. Say the only omission is $AB$.
Then $B$ also saturates, and the universal double $D$ has
nonempty support inside $R_A\cap R_B$. Split at one of its
support points. We have $|\Delta|\le4$ and $K\subseteq H_A$,
so $L$ is nonempty. Neither $R_A$ nor $R_B$ crosses $K,L$,
since $k<2k-8$ and both meet $K$. All double supports are
contained in their union and avoid $L$. Thus $L$ uses only
$C$ and $|L|\ge k-4$. Every $w$ sees $L$ and the three nonempty
disjoint double supports, a contradiction.

Now suppose there are at least two distinct omissions.
All ports other than $A$ meet some $w$. The possible omissions
are $AB,AC,AF$, so $D,E$ are universal and have nonempty,
disjoint supports inside $R_A=V_1$. Split at $x\in R_D$.
The exact distance-two cap at $A$ is exhausted by all $W$,
the root, the two other anchors, and the three remotes in
$H_A\setminus R_A$. In particular $A$ must be adjacent to $E$,
since otherwise it sees $E$ at distance two via anchor 1.
Thus $x$ sees $E$ at distance two via its neighbor $A$.
It cannot be adjacent to $E$ because the $D,E$ masks together
see all three anchors. It also sees all $W$ and the two
anchors of $D$ at distance two. These give $|\Delta|\le3$.
Since $K\subseteq H_A$, the set $L$ is nonempty. Port $A$
cannot cross $K,L$, so $R_A,R_D,R_E$ all avoid $L$.

For the other ports, $|H_F|\le(k-6)+(k-2)=2k-8$. The nonempty
support of the opposite universal double gives
$|R_B|,|R_C|\le k-4$. If $AF$ occurs, some $w$ touches $B,C$
together, giving $|R_B|,|R_C|\le k-6$ by the other singleton's
three solos. If $AF$ does not occur, $AB,AC$ both occur and
$a_B,a_C\le k-7$. In either case $|H_B|,|H_C|\le2k-8$.
Hence no support crosses $K,L$, since crossing requires
$|H_J|\ge2k-7$.

The set $K$ has size at least $k-2>|R_A|$, so at least one
port among $B,C,F$ is used in $K$. Consequently $L$ uses at
most two of those ports and has size at least $k-4$ from the
closed remote degree bound and $|\Delta|\le3$. A touched
quartet containing all ports used on $L$ would see $L$ and
the nonempty, disjoint supports $R_D,R_E$ outside $L$.
That exceeds its support cap.

The only way a pair of $B,C,F$ is never touched together
is when exactly two omissions $AX,AY$ occur, with that pair
being $X,Y$. Write $J$ for the remaining member of $B,C,F$.
Thus the surviving configuration has touched quartets
$D,E,J,X$ and $D,E,J,Y$. The set $L$ uses both $X,Y$, the
set $K\setminus R_A$ is nonempty and consists of $J$-solo
remotes, and $|\Delta|\le3$. This is the part left open
by this argument.
