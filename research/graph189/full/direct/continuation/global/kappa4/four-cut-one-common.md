# One common label on a four-cut at degrees 26 through 30

Assume the original Graph 189 hypotheses, a minimum four-cut, and high populations $x\le y$ on its two sides. Let $26\le k\le30$, $n\ge6k-19$, and $y>4k$. Then the support classification, by the existing strict large-side version, gives a two-common-label conclusion unless there is one common label and all high supports use at most one additional label. The latter case is impossible by the following argument. The case of zero common labels and singleton supports still uses the private quota.

Write $i_0$ for the unique common label. An opposite contact to it sees all $x$ high small-side vertices at exact distance two, so $x\le k$. For each of the three residual labels $i$, let $Q_i$ be its high direct large-side contacts avoiding the common label. Let $P_D$ be the union of these sets and $P_C$ the high large-side ports incident to the common label. Let $H_N$ be the high large-side nonports at distance two from the common label and $G_N$ the remaining high large-side nonports. Write $Z_i$ for the vertices of $G_N$ at distance two from $i$. These are the intermediate sets in Graph189PrivateQuota.residual_singleton_quota.

Set $r=k-2$, $q=3r-|P_D|$, $h=k-|H_N|$ and $d_i=r-|Q_i|$. We have $\sum_i d_i\le q$, because $|P_D|\le\sum_i|Q_i|$. Each of the three row inequalities gives $|P_C|+|G_N|\le d_i+|Z_i|$, so $|P_C|\le d_i$ and $3|P_C|\le q$. The final quota's available slack is

$$\sigma=3(5k-4)+x-3(x+y)\le60-2k\le8,$$

using $x+y\ge n-5\ge6k-24$. The proof of that quota pays at least $2q+3h$ of this slack. Indeed its bound $|P_D|+3(|P_C|+|G_N|)\le3r+x+6$ leaves the additional nonnegative difference, while $3y=|P_D|+3(|P_C|+|G_N|)+2|P_D|+3|H_N|$. Thus $q\le4$, $|P_C|\le1$, and $h\le2$.

For every residual label, the size of $Z_i$ is bounded below by

$$|Z_i|\ge |P_C|+|G_N|-d_i
=y-4k+6+q+h-d_i\ge k-18+h.$$

In particular, any residual anchor at distance two from all $H_N$ would see at least $2k-18>k$ positive even vertices.

If $P_C$ is empty, the sole contact of the common anchor on the large side is the unique low vertex $z$. Its edge to the common anchor has at least three common neighbors from the edge-order bound, since the anchor is high and $n>5k+4$. All these neighbors lie on the separator, so $z$ touches every label. For a vertex of $H_N$, its two-step route to the common label has middle vertex on the large side. Thus every such route uses $z$, and every member of $H_N$ sees every residual label at distance two. This is impossible.

If $|P_C|=1$, then $q\ge3$ and $\sigma\ge6$. Consequently $k$ is 26 or 27, $h=0$, and $x\ge k-2$ because $\sigma\le x-3k+60$. Every actual large-side common-label contact has at least two labels by the boundary debit at that contact, since it sees all $x$ small-side high vertices. If there is only one such contact, a second label of it is at distance two from all of $H_N$. If there are two such contacts, the exceptional low vertex is on the large side and the small side is wholly high. Its high vertices touch at most two anchors, so the degree bound gives $x\ge k-1$. The boundary debit now forces at least three labels at each of the two large-side contacts. They share a residual label, and every member of $H_N$ has a two-step route to that label via one of the two. This is again impossible.

The argument uses the intermediate inequalities already derived in Lean and a new analysis of their finite slack. The new graph integration is at paper level.
