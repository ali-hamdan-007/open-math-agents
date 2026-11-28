# Private and residual singleton quotas

Let a cut with label set $S$ separate sides $A,B$, and let $X,Y$ be their respective high populations, where high means degree at least the ambient second-smallest degree $k$. Let $C\subseteq S$ consist of labels common to the high vertices of $A$. Set $D=S\setminus C$, $s=|S|$, $c=|C|$, and $d=|D|>0$. Suppose every high vertex of $A$ meets at most one member of $D$, and choose a high $A$ representative $a_i$ on each $i\in D$.

For arbitrary opposite windows $Z_i\subseteq B$ at exact distance two from $i$, one has

$$
\sum_{i\in D}|Z_i|\le |X|+d(c+1).
$$

Indeed, $a_i$ meets at most $c+1$ cut vertices. Its closed internal neighborhood therefore contains at least $k-c$ vertices, of which at least $k-c-1$ are high. Each of these high vertices either neighbors $i$ or sits at exact distance two from $i$. The $i$-quota counts the latter together with $Z_i$, because the two sides are disjoint. Hence $|Z_i|\le |X\cap N(i)|+c+1$. The high $A$ contact sets for distinct residual labels are disjoint, so summing proves the window inequality. The argument allows a low vertex in any position.

For the full high population bound, split the high ports in $B$ into $P_C$, those touching a common label, and $P_D$, the remaining ports. Split the high nonports into $H$, those at distance two from at least one common label, and $N$, the remaining nonports. Let $Q_i=P_D\cap N(i)$ and $Z_i=\{v\in N:\operatorname{dist}(i,v)=2\}$. The positive-even witnesses of $a_i$ in $Y$ include all of $P_C$, all of $Q_i$, and $N\setminus Z_i$. For the last claim, an odd distance between the high pair would be three. Any separator vertex on a shortest three-edge path has distance at least two from its nonport end, so is adjacent to $a_i$ and at exact distance two from that end. It must be a residual label by the definition of $N$, and hence equals $i$.

The pointwise separator debit at $a_i$ leaves at most $r=k+1-d$ even witnesses in $Y$. It follows that $|Q_i|\le r$ and $|P_C|+|Q_i|+|N|\le r+|Z_i|$. The $Q_i$ cover $P_D$, so $|P_D|\le dr$ and

$$
d(|P_C|+|N|)+|P_D|\le dr+|X|+d(c+1).
$$

Adding $(d-1)|P_D|\le(d-1)dr$ and $d|H|\le dc k$, the latter from the common-label even quotas, gives

$$
d|Y|\le d(sk-d(d-1)+c+1)+|X|.
$$

For $C=\varnothing$ this is the all-private quota. For $c=1$ or $c=2$ an opposite contact at any common label sees all of $X$ at exact distance two, so $|X|\le k$. Those are the exact graph inputs for the private and small-common-label inequalities of a valid terminal band.
