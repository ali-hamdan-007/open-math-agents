# The three largest four-port orders are impossible

Use the (a,s)=(4,4) setup in degree-five-four-port-overlap.md. Thus there are five anchors A, four ports P, a connected component D=P∪R, and h=|R|. Each member of R has a nonempty port mask. Every port touches an anchor. All vertices of D and all anchors have degree at least k, with k≥7. As in the earlier note, write S_p=N_R(p), B_p=N_R(S_p)−S_p, and c_p for the number of other ports at distance two from p. We have |S_p|≤k−1 and |B_p|≤3−c_p. The latter follows because a port has the k−3 fixed distance-two witnesses K∪{z}. An adjacent port q also gives S_q∖S_p as further distance-two witnesses for p in R. Any anchor touching ports P' has at most k−1 vertices in the union of their S_p: this union is at distance two, and there is an outside witness from a missed anchor or a missed port.

**Claim.** h≤2k+1.

Let a count the private vertices, those with one-port masks. Every private x∈S_p has a neighbor y outside S_p, because it has at most |S_p|≤k−1 possible neighbors in S_p∪P. If y touches q, then x∈B_q. Thus
\[
a\le \left|\bigcup_p B_p\right|\le\sum_p|B_p|\le12-\sum_p c_p.
\]
Write e for the sum of |M(x)|−2 over masks of size at least three, and let σ=4(k−1)−Σ_p |S_p|. Since Σ_p |S_p|=2h−a+e, this already gives h≤2k+4. Suppose h≥2k+2 and put t=2k+4−h∈{0,1,2}. The same identity yields
\[
a=12-2t+\sigma+e,\qquad \sigma+e+\sum_p c_p\le2t\le4.
\]

No anchor touches three ports. For three such ports the sum of their support sizes is at least 3(k−1)−σ. A core vertex accounts for at most two of these incidences except for total excess at most e. The union of the supports would have size at least
\[
\frac{3(k-1)-\sigma-e}{2}\ge\frac{3(k-1)-4}{2}>k-1.
\]
for k≥7. This contradicts the anchor bound.

We next show that every |S_p|≤k−2. If |S_p|=k−1, take an anchor α touching p. It has only one remaining even-distance witness available outside R, and it touches at most two ports. If it sees all other anchors, every omitted port is at distance two via one of those anchors. There are at least two omitted ports, impossible. Thus α misses exactly one anchor β (each missed anchor is at distance two through z), and no omitted port may be at distance two from α. Each omitted port must consequently touch only β, since adjacency to any other anchor gives a two-edge route. There are at most two ports touching β, so α touches two ports and β touches the two complementary ports. The two unions of their support sets cover R, but each has size at most k−1. This contradicts h>2k−2.

Hence σ≥4. The displayed inequality forces t=2, σ=4, e=0 and every c_p=0. Every support has size k−2. The private count equals 12, so all B_p have size three, are disjoint, and consist only of private vertices. Every remaining vertex has a two-port mask.

In this equality case each port has exactly three private vertices. To see this, classify each private vertex by an ordered pair p→q, where p is its unique port and B_q is its unique boundary set. Every private vertex in S_p needs at least two neighbors in R∖S_p, because it has at most |S_p|=k−2 neighbors in S_p∪P. For a vertex of type p→q, every such neighbor is private to q: if another port met that neighbor, the original vertex would belong to a second boundary set. These neighbors belong to B_p. Thus a nonempty type p→q forces at least two vertices of type q→p, and conversely. For each p, the three members of B_p therefore all come from one type q→p, since two incoming types would each have size at least two. Their reverse type p→q is the only outgoing one, and it has size three because B_q also has exactly three incoming vertices. The three private vertices of each port follow.

For every occupied two-port mask {p,q}, the ports are adjacent, since otherwise they are at distance two although c_p=0. Its size m_pq=|S_p∩S_q| is at least k−5, since S_q∖S_p is at distance two from p and can have at most three members. The sum of all occupied pair sizes is h−12=2(k−5), so at most two masks are occupied. Every port has k−5>0 vertices on occupied pair masks because it has only three private vertices. Thus there are two disjoint occupied pairs, each of size k−5. For a pair {p,q}, the three members of S_q∖S_p and the three members of B_p are all at distance two from p, so they coincide. In particular B_p contains only the private vertices of the partner q.

Finally the two port pairs and their support sets give a partition of D into two nonempty sides. A cross edge between ports would send all k−2>3 neighbors of one port into the other port's distance-two set, impossible. There are no cross port–core edges by the definition of the sides. A cross edge in R would put its endpoint opposite any port touching the other endpoint into that port's boundary; the boundary consists only of private vertices on that port's own side. Thus there are no cross edges at all, contrary to D being connected.

The remaining interval is 2k−3≤h≤2k+1, reducing the 48 cases with 7≤k≤12 to 30.
