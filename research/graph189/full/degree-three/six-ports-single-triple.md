# The six-port triangle with one triple-visible remote

**Theorem.** In the triangular six-port template, suppose exactly one remote is visible from all three anchors and the induced graph on the other remotes is 2-connected. If $k≥32$, the original graph has a spanning path.

The root $z$ has eccentricity three, its three anchors form a triangle, and its middle layer comprises $k-6$ common middles $W$ and six ports of respective anchor masks $1,2,4,3,5,6$. Every nonroot degree is at least $k$, the order exceeds $3k$, and every vertex has at most $k$ positive even-distance partners. Let $D$ be the remote layer, $c=|D|≥2k-3$, $t$ the unique triple-visible remote, $F=G[D∖\{t\}]$, and $d$ the number of nontriples visible from two anchors. Visibility means adjacency to a middle neighbor of the anchor.

## Support bounds

Each anchor sees its three missed ports at distance two via another anchor. Its remote visible set has size at most $k-3$, and the three sizes sum to $c+d+2$. Thus $c≤3k-11-d$ and $|F|≤3k-12-d$. Each anchor has at least $c-2(k-3)+1≥4$ exclusive remotes, by complementing the other two visible sets, whose intersection contains $t$. Each exclusive is a solo of the unique singleton port at its anchor.

Write $R_J$ for the full remote support of a port $J$, $H_J$ for its closed neighborhood inside $G[D]$, and $a_J=|N(J)∩W|$. Every singleton has $|R_J|≤k-3$. A double has $|R_J|≤k-7$ since the at least four exclusive remotes at either incident anchor lie outside its support. At $J$ the root, the anchors not in its mask and its $k-6-a_J$ missed common middles lie at distance two, so
\[
 |H_J∖R_J|≤a_J+3\quad\text{for singleton ports},\qquad
 |H_J∖R_J|≤a_J+4\quad\text{for double ports}.
\]
Every nontriple touches at least one port and no common middle. Its supporting masks are contained in the same one or two visible anchors, so it has at most three port neighbors, just one when exclusive. Its closed full remote neighborhood has size at least $k-2$.

Each common middle meets at least three ports, by its degree: outside the ports it has at most $k-7$ common peers, three anchors and $t$. It meets at most four. If it meets exactly five, choose any anchor incident to its omitted port, whether singleton or double. All remotes outside that anchor's visible set are nontriple and supported by a different port; there are at least $c-(k-3)≥k$. They and the root are at distance two. If it meets all six then all nontriples and the root are at distance two. Both cases are impossible. Even the looser bound of six ports shows that a common middle misses at most three peers.

## A cycle on the remote vertices to be used

If $t$ has a common-middle neighbor put $L=F$; otherwise put $L=G[D]$. In the first case $δ(F)≥k-4$. Any three nontriples together touch at most $3+2\min(d,3)$ ports counted with multiplicity, so their degree sum in $F$ is at least $3k-6-2\min(d,3)≥3k-10-d≥|F|+2$. Here $2\min(d,3)≤d+4$.

An independent set $I$ of size $k-3$ in $F$ would have every pair sharing a neighbor since $2(k-4)>|F|-|I|$. For any $x∈I$ touching port $J$, count its other $k-4$ independent companions at distance two, the $a_J$ common neighbors, and two further vertices. If $x$ is visible from two anchors, count both. Otherwise count its visible anchor and a foreign port: the solo's closed remote neighborhood has size at least $k$, so a neighbor outside the anchor's visible set must exist and must be a nontriple with a different supporting port. Thus $a_J≤2$ for every touched port. The closed remote neighborhood of $x$ lies inside $H_J$ and is disjoint from the other members of $I∩R_J$. We obtain $|I∩R_J|≤|H_J|-(k-2)+1$, at most five per singleton and two per double. These six supports would cover at most 21 independent vertices, less than $k-3$. Thus $α(F)≤k-4$ and each independent triple has degree sum at least $3α(F)$.

In the second case, each nontriple has degree at least $k-3$ in $L$. The triple $t$ has degree at least $k-5$ there if it touches at most five ports. If it touches all six, then every nonneighbor in $F$, every common middle and the three anchors are at distance two from it, so its degree in $L$ is at least $|F|-3≥k-5$. In particular $L$ is 2-connected since $t$ has two or more neighbors in $F$. An independent triple of nontriples has degree sum in $L$ at least $3k-3-2\min(d,3)≥c+2$. A triple containing $t$ has degree sum at least $3k-7-2\min(d,2)≥c+2$ because $2\min(d,2)≤d+2$. All independent triples also have degree sum at least $3k-11$ by the individual degree bounds.

An independent set of $k-3$ in $L$ has a nontriple part $I_F$ of size at least $k-4$. All pairs in $I_F$ have a common $L$-neighbor since $2(k-3)>c-|I_F|$, the latter being at most $2k-7-d$. The two extra witnesses above give $a_J≤3$ for each touched port. The closed neighborhood argument with the improved double-support bound gives at most six independent members per singleton and three per double, hence $|I_F|≤27$. At $k=32$ already $k-4=28>27$, so $α(L)≤k-4$. Thus $3k-11≥3α(L)$.

In each case $L$ is 2-connected and every independent triple has degree sum at least $s=\max(|L|+2,3α(L))$. Bauer et al.'s circumference bound supplies a cycle of length at least $\min(|L|,|L|+s/3-α(L))=|L|$. The statement also applies vacuously to degree sums if no independent triple exists. [Bauer et al., Theorem 10](https://ris.utwente.nl/ws/files/6736746/Bauer90long.pdf).

## Inserting the ports and joining the path

Withhold any singleton port $E$ and choose one of its exclusive solos $x$. Fix a Hamilton cycle of $L$ and mark either cycle edge at $x$ for deletion. Among the other five ports call one high if $a_J≥9$ and low otherwise. At least one is high: if all five are low the total port-to-common incidences are at most $5·8+|W|<3|W|$ for $k≥32$ (already $66<78$ at $k=32$), contradicting the common-middle lower bound. At most four ports are low.

For each low $J$, put $X_J=R_J∩V(L)$. The degree of $J$ counts at most $a_J$ common middles, two anchors and the five other ports outside the remote layer. The cycle omits at most $t$ from the full remote layer, so $|X_J|≥k-a_J-8$. Along the cycle the edges leaving $X_J$ terminate at vertices in $H_J∖R_J$. Each such vertex is incident to at most two cycle edges. Hence the number of cycle edges with both ends in $X_J$ is at least
\[
 |X_J|-|H_J∖R_J|≥k-2a_J-12≥4.
\]
The marked edge cannot be among them because $x$ is a solo of $E$. Greedily select distinct eligible edges for all low ports and subdivide each selected edge by its assigned port. The edges may share endpoints: subdivision of distinct edges of a cycle always gives a cycle. Deleting the marked edge now produces a remote path starting at $x$ and visiting all of $L$ and all low ports.

When $t$ lies outside $L$, reserve one of its common neighbors $w_0$. Otherwise reserve any $w_0∈W$. Assign two distinct common neighbors in $W∖\{w_0\}$ to every high port, with all assigned vertices different. For any family of one to four high ports, the union contains at least eight choices after reserving $w_0$, enough for two per port. For five, their total of at least 45 incidences needs at least $\lceil45/4\rceil=12$ common middles before the reservation, because each common middle meets at most four ports. This verifies Hall's condition on two copies of each port.

Make each chosen pair an oriented common–port–common block, all remaining common middles being singleton blocks. Two blocks are compatible if each one's tail is adjacent to the other's head. Each block is incompatible with at most six others because distinct heads and distinct tails belong to $W$ and each common middle misses at most three peers. There are $b=k-6-\#\{\text{high ports}\}≥21$ blocks, so every nonadjacent pair has degree sum at least $2(b-7)≥b+1$. Ore's criterion gives a spanning block path starting at the singleton $w_0$ and ending at any specified different block. [Ore's Hamilton-connectedness criterion](https://doi.org/10.1002/jgt.3190180808).

Start at $t$ and enter $w_0$ when $t$ lies outside $L$, and otherwise begin at $w_0$. Follow the block path. From the final common middle visit an anchor different from the anchor of $E$, the root, the other remaining anchor, and finally the anchor of $E$. Follow by $E,x$ and the remote path starting at $x$. Every common middle, port, anchor and remote occurs exactly once.
