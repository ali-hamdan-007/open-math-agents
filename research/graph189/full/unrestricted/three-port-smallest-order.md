# Degree-five root: the three/four-port frontier

Let (z) be the unique vertex of degree five and let every other vertex
have degree at least (k\ge 7). Put (A=N(z)), and suppose that
(G-N[z]) has a pure second-layer component (K) and one other component
(D). Write (P=D\cap N_2(z)), (s=|P|), (R=D-P), (h=|R|),
(r=|K|), and (a=k-r).

## A shell lemma

For (a=3) or (4), the shell (S=G[A\cup\{z\}\cup K]) has a spanning
path between any prescribed distinct anchors. Adjoin a degree-two marker at
the prescribed anchors. The augmented order is (r+7=k-a+7). A vertex of
(K) has shell degree at least (k), while an anchor has shell degree at
least (k-s), since its only possible lost neighbors are the (s) ports.
Cycle closure completes (K) and all anchor--(K) pairs because

\[
  k+(k-s)\ge k-a+7.
\]

For ((a,s)=(3,3),(4,3),(4,4)), this holds for (k\ge7). In the completed
graph, (K) is a clique complete to all five anchors. Since (r=k-a\ge3),
it has an anchor-to-anchor spanning path containing an anchor--(z)--anchor
segment; separate the other three anchors by vertices of (K) and put any
surplus (K)-vertices consecutively. The marker closes this to a Hamilton
cycle. Reverse closure and delete the marker.

## The first three-port order is traceable

Assume ((a,s)=(3,3)). Then (r=k-3), there is no fourth layer, and every
member of (R) is adjacent to a port. The order identity is

\[
   n=k+6+h.
\]

Thus (n>3k+2) implies (h\ge2k-3). If (h=2k-3), then (G) is
traceable for every (k\ge7).

First note two consequences of 2-connectivity. At least two ports have a
neighbor in (R); otherwise deleting the sole such port separates (R)
from the shell. Moreover

\[
 \left|\bigcup_{p\in P}N_R(p)\right|\ge2,
\]

since if the union were the singleton \(\{x\}\), deleting (x) would
separate the nonempty set (R-\{x\}) from the shell. The path-closure
threshold after adjoining one marker or leaf is

\[
  |D|=h+3=2k.
\]

Every vertex of (R) has all its neighbors in (D), hence degree at least
(k), so path closure completes (R) to a clique.

If exactly two ports (p,q) meet (R), the inactive port (t) is adjacent
to one of them, say (p), because (D) is connected. The two nonempty
sets (N_R(p),N_R(q)) have union of size at least two, so they have distinct
representatives (x,y). Add a leaf \(\ell\) at (t). In the closure there
is the spanning path

\[
  \ell,t,p,x,\quad R\text{ in clique order ending at }y,\quad q.
\]

After closure reversal the degree-one vertex \(\ell\) is still an endpoint;
delete it and append a shell path at any anchor of (t).

It remains that all three ports meet (R). Choose two ports which can be
assigned distinct anchor neighbors; such a pair exists because
2-connectivity forces (D) to meet at least two distinct anchors. Call the
pair (p,q), the remaining port (t), and orient it so that

\[
  |N_R(q)\cup N_R(t)|\ge2.
\]

This orientation always exists: failure in both orientations would make
all three port-neighborhoods the same singleton. Choose distinct
(x\in N_R(q)), (y\in N_R(t)), and adjoin a marker (b) adjacent only to
(p,q). In the closure the path

\[
 p,b,q,x,\quad R\text{ in clique order ending at }y,\quad t
\]

is spanning. Closure reversal need not keep (b) at an endpoint, but
either outcome expands through the shell. If (b) is internal, replace
(p-b-q) by (p-\alpha-S-\beta-q), using the distinct assigned anchors.
If (b) is an endpoint next to one of these ports, append a shell path
whose incident endpoint is an anchor of that port and whose other endpoint
is any different anchor.

Consequently the entire ((3,3)) residual satisfies (h\ge2k-2).
