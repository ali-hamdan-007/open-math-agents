# Private ports across a separator and geodesic width

In a hypothetical Graph 189 counterexample let S be a minimum separator of size s≥3, let A,B partition the components of G−S into two nonempty groups, and let X,Y be the respective counts of high vertices. Assume A contains a high vertex x with no neighbor in S. Let P be the number of high B ports adjacent to exactly one member of S. Define

    L = ceil(2(n−2k)/(k+1))−1,

which is at least s by lowblock/geodesic-width-and-order.md. Then

    (1)  2Y−2(k−s)−sk ≤ P ≤ k−s + kX/L.

Every high B nonport has distance four from x. The second layer from x lies outside B, and when a fourth layer is present this separating second layer contains at least s vertices. Thus there are at most k−s high B nonports. Every label has at most k B contacts, since a contact in A sees all of them at distance two. Summing the contact incidences over the at least Y−(k−s) high B ports yields the lower bound in (1).

Let b_i count the private high B ports at label i; let t_i count the neighbors of x adjacent to i. Whenever b_i t_i>0, select one such neighbor u and a private B vertex y on i. The geodesic x,u,i,y has common-neighbor counts |N(x)∩N(i)|=t_i and |N(u)∩N(y)|=1. Indeed no edge crosses between A and B and y touches only i in S. The order-versus-geodesic-width inequality then yields t_i≥L. When t_i=0 all corresponding private y are at distance four: a three-step path must use i on its last step and an A contact on that label on its first. The private vertices in these latter classes together number at most k−s, as above. Now each u adjacent to x is in A, and the b_i summed over its labels count distinct vertices at distance two from u. Hence

    L(P−k+s) ≤ Σ_i b_i t_i ≤ k d(x) ≤ kX.

The last bound allows the sole low vertex in A. This proves the upper bound in (1). Neither estimate requires B to be connected or to contain a nonport.

## A nonvacuous uniform consequence for counterexamples

Consider any sequence of hypothetical counterexamples with k and s tending to infinity; suppose that for each graph the smaller high group of a minimum cut partition contains a high nonport. Then

    limsup s²/k ≤ 27/8.

Here are the dependencies and limiting estimates. The earlier unrestricted theorem in global/two-thirds-exterior-degree.md bounds s=O(sqrt(k)) and gives an optimized exterior good block of minimum high/nonexceptional internal degree q≥(2k−2sqrt(3k)−5)/3. If this block is in the large-cycle alternative, the s connectors give n≥(s+5)q+2s−1 (or the stronger terminal bound for h≥3). The small-block alternative in lowblock/geodesic-width-and-order.md gives n≥(1−o(1))sk because s=O(sqrt(k)): the order contributions are a concave minimum of a term of order k² and a term (s+O(1))(k−s+O(1)), for both the whole and terminal block. Consequently λ=n/(sk)≥2/3−o(1).

The universal smaller-side bound root/minimum-cut-populations.md gives X≤(2+o(1))k. Thus Y/(sk)=λ+o(1). In proving the limsup one can restrict to subsequences with s/sqrt(k) bounded below by a positive constant. On such a subsequence λ is bounded above by the global n=O(k^(3/2)) theorem, so a further subsequence has λ→λ₀≥2/3. The high cross-pair product XY≤kX+sk² gives X/k≤1/λ₀+o(1), and L/s→2λ₀. Inequality (1) now gives

    (2λ₀−1+o(1))sk ≤ P ≤ (1/(2λ₀²)+o(1))k²/s.

It follows that limsup s²/k≤1/(2λ₀²(2λ₀−1))≤27/8. In particular above the asymptotic ratio sqrt(27/8) the unique giant component of a minimum cut has all off-giant high vertices adjacent to the separator. This improves the unrestricted known coefficient (3/2)sqrt(3) for this branch. The exact finite statement is (1), together with the cited integer order and width bounds.

## Assigning arbitrary ports and the stronger order bridge

There is a stronger finite form valid for every high x in A, including ports. Set r=|N_S(x)| and D=ceil(2(n−2k)/(k+1)). Then

    (D−r)(Y−(r+1)k+s−r) ≤ k d_A(x)+sk ≤ kX+sk.

Here D≥s+1>r. Call a high B member y good if some x-to-y three-step geodesic goes through u in A and then i in S. Every other high B member is either at even distance from x or at exact distance two from an anchor touching x: in any three-step geodesic that is not of the indicated form, the first step goes to S. All cross distances are between two and four. At most k−s+r opposite vertices are even, by the s-vertex boundary of the closed internal A-neighborhood of x. The r anchor quotas pay at most rk other vertices. There are therefore at least Y−(r+1)k+s−r good y.

Assign each good y to one i from such a geodesic. The width bound for x,u,i,y is |N(x)∩N(i)|+|N(u)∩N(y)|≥D. The latter count is at most the size of y's S-support, because u is in A and y is in B. Apart from the at most r anchor vertices in the former intersection, it counts A-neighbors of x touching i. Thus these A-neighbors number at least D−r−|N_S(y)|. The same neighbors each see y at distance two. Because the assignment chooses just one i for each y, double counting over u in N_A(x) gives at most k d_A(x), without repeatedly charging a y to the same u. The sum of |N_S(y)| over these assigned vertices is at most sk by the individual contact-class caps. This proves the display.

The new order theorem n≥s(k−s+2) in root/longest-cycle-exterior.md gives λ₀≥1 on all the subsequences used above. Write ρ=lim r/s after extracting a further subsequence, and let c=lim s/sqrt(k). The general display yields

    (2λ₀−ρ)(λ₀−ρ)c² ≤ 1/λ₀.

In particular a single small-side high vertex with r=o(s) forces limsup s²/k≤1/2 regardless of low placement or whether either side is shallow. If s/sqrt(k)→1 then every small-side high vertex has r/s≥(3−sqrt(5))/2−o(1). These implications use only the finite inequality and the new bridge; whether the bridge is used is independent of the exact combinatorial lemma.
