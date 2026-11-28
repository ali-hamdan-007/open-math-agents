# A connectivity-dependent order bound and width of every three-step geodesic

Write k for second-smallest degree and s for vertex connectivity of a qualifying graph G. If s≥3, then
    |G|≤2k+s(k+1)/2  implies traceability.
As a consequence, in every hypothetical nontraceable such graph and along every geodesic x,i,j,y of length three with both x and y high,
    |N(x)∩N(j)|+|N(y)∩N(i)|≥s+1.
The same pair of neighborhoods can instead be used directly to deduce an order bound with no connectivity hypothesis. These inequalities concern arbitrary degrees and cut sizes.

## The order bridge

Set h=ceil(k/2), t=floor(k/2) and M=2k+s(k+1)/2. The half-connectivity result deals with s≥t, so assume 3≤s≤t−1. Take a longest path in a hypothetical counterexample. By all-near-spanning.md it omits a component C containing a high vertex (an exterior consisting only of a low singleton is excluded). Apply the unrestricted contact matching estimates of ../sep/k10/uniform-matching.md. They allow an exceptional low anywhere. In a large 2-connected component with least high degree q≥h and order b≥2q, the bound is n≥(s+5)q+2s−1>M. In a large leaf block with order ≥2q−1 it is n≥(s+5)q+2s+h−4>M; here h≥4.

For a remaining two-connected C let b=|C|≥h+2. Its s matched contacts can be increased to j≥max(s,k−b+1): every high member needs k−b+1 contacts if that number is positive, and the at least b−1 high members suffice for that many by b≥h+2 and the minimum cover bound. The matched gaps and tails in the near-Hamilton-connected component show
    n≥(j+2)b+j−1.
For b≥k−s+1 the s expression increases with b, starting at (s+2)k−s²+1, which exceeds M by s(k/2−s−1/2)+1. For h+2≤b≤k−s+1 the expression using j=k−b+1 is concave in b. At its upper endpoint it has the same bound. At h+2 it gives t²+4t for even k=2t, and t²+5t+1 for odd k=2t+1. The maximum M at s=t−1 is respectively t²+7t/2−1/2 and t²+4t+1. These are strictly smaller.

For a remaining terminal leaf block the cited bound gives
    n≥3h−1+min((h+1)(k−h+2),(s+1)(k−s+2)).
The second expression after adding 3h−1 exceeds M by at least (s+1)k/2−s²+s/2+1, which is positive. For the first expression, at even k it gives t²+6t+1, and at odd k it gives t²+7t+6. They also exceed the same maxima of M. All exterior alternatives force n>M. This proves the order bridge.

## The geodesic inequality

For any induced wedge u,w,v put J=|N(u)∪N(w)∪N(v)|−d(u)−d(v) and e(w) its positive-even count. The independently formalized wedge order inequality gives
    (k+1)J≤4k+2−n+k(d(w)+e(w)−d(u)−d(v)).
On a geodesic x,i,j,y apply this to x,i,j and y,j,i. The sum of their degree/exact-even terms equals e(i)+e(j)−d(x)−d(y)≤0 for high endpoints. For any wedge the defect J equals |N(w)−(N(u)∪N(v))|−|N(u)∩N(v)| and the first set includes both nonadjacent endpoints. Thus if D is the sum of the displayed two common-neighbor counts then
    (k+1)(4−D)≤8k+4−2n,   so   n≤2k+(k+1)D/2.
Combining with the order bridge forces D≥s+1. These two sets of common neighbors are disjoint: an intersection would be adjacent to x and y, against their distance three.

## All large minimum-cut sides inherit the ambient odd distances

Delete a minimum separator S of order s, and let B be an induced component. If a high-high pair x,y∈B has ambient distance three but no B path of length three, then some ambient three-step geodesic consists of only one exterior anchor, unless the order bridge already proves traceability. Indeed, if all shortest paths use two exterior vertices, choose x,i,j,y with i,j∈S. Every common neighbor of x,j and of y,i must belong to S, since otherwise there would be a shortest path with at most one exterior point. Their disjoint union then has size at most s, contrary to the geodesic inequality.

If all ambient two-edge paths between B endpoints can be relayed inside B, a single-exterior-anchor path can be relayed as well. Thus all high–high B-terminal distances through length three transfer in a counterexample, irrespective of the size or graph on S. For instance at k≥6s−5 the two-edge transfers follow from large-side-metric.md whenever B is wholly high and each anchor has a high neighbor in another side. Under these hypotheses, if each B vertex has at least k−δ(B) outside positive-even witnesses, then connected B itself satisfies Graph 189. In a minimum-order counterexample it is traceable at arbitrary |B|. The former two-sided configuration of three anticomplete dense blocks coming specifically from a failed three-step transfer is therefore excluded; the remaining possible failure in these parameter ranges comes from insufficient outside even witnesses or from incompatibility of the resulting spanning path endpoints.

## An unrestricted sharper order bound

The order inequality summed through a root also improves the leading constant of the unconditional order bound. Take a vertex x of degree exactly k (so x is high), put B=L₂(x), and let C be the high vertices in L₃(x). The other positive-even layers together have at most k vertices. A possible layer-five point is low, so the one low exception together with x, the k first neighbors and those even layers gives
    |C|≥n−2k−2.
For every y∈C choose one geodesic x,i(y),j(y),y. Each N(x)∩N(j(y)) member has distance exactly two to y. Thus summing this first cardinality over y costs at most k², since the k first neighbors of x each see at most k different targets at even distance. The second cardinality |N(y)∩N(i(y))| is at most the number of B-neighbors of y, because such common points are necessarily in L₂(x). Summing over y costs at most k|B|≤k²: for every b∈B each y∈C adjacent to b has distance two from any fixed first-layer predecessor of b. Therefore
    (n−2k)|C|≤(k+1)k²,   (n−2k)(n−2k−2)≤(k+1)k²
when n≥2k+2. Equivalently every qualifying graph has
    n≤2k+1+floor(sqrt(k²(k+1)+1)).
This bound uses the wedge inequality but neither nontraceability nor any connectivity lower bound. It improves the coefficient of k^(3/2) from sqrt(3) to one in the previous unconditional large-k bound; one can still take the minimum with the degree-sensitive quadratic theorem at small k.

For endpoints of a three-step geodesic on opposite sides A,B one also has D≤w(x)+w(y), where w denotes the count at positive even distance outside the vertex's own side. Indeed N(x)∩N(j) consists of outside-even witnesses of y, and N(y)∩N(i) similarly consists of outside-even witnesses of x. Thus high opposite vertices x,y with w(x)+w(y)≤s must have even distance in a counterexample. For each outside-allowance-deficient x this entails w(y)≥s+1−w(x) on every high vertex of the opposite side except the at most w(x) points at even distance from x.
