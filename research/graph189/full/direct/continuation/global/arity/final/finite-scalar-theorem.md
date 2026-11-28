# A finite separator certificate for Graph 189

Let G be a connected simple finite graph on n≥2 vertices. Let k be its second-smallest degree, counting repetitions, and suppose each vertex has at most k other vertices at positive even graph distance. The analysis below derives a contradiction from failure of a Hamiltonian path. It uses the graph results catalogued below and a reproducible finite arithmetic check. The companion Lean module verifies the terminal interval calculations and the population bound used at every minimum cut.

## Prior degree, separator and width inputs

Write s=κ(G), e=Δ(G)−k and call the vertices of degree at least k high. The results for s≤4 and k≤25 are summarized with their individual proofs in ../../../sep/cover/fifth-connectivity.md. The basic connectivity obstruction 3s<k is in ../../../sep/cover/third-connectivity.md. Thus take s≥5, k≥26, 3s<k. For this certificate the stronger one-fifth connectivity theorem is unnecessary.

1. The universal completion of a minimum-degree vertex gives n≥(s+1)(k−s+2)−1. When a minimum-degree vertex avoids all minimum cuts it gives n≥(s+2)(k−s+1)−1. See ../../../root/universal-minimum-order.md, including the proof and reference to Nikoghosyan's cycle Corollary A.
2. Every group on either side of a minimum separator contains a high vertex. Singleton cut components are excluded in ../../../root/nontrivial-cut-sides-and-exterior-cycle.md. With X≤Y the high populations of any two opposing groups, XY≤kX+sk² and X≥k−s. Thus n≤2k+1+sk²/(k−s): in fact X≤k+sqrt(sk²) implies convex X+k+sk²/X has its maximum at X=k−s or at the positive root X²=kX+sk²; the second endpoint is no larger than the first for k>3s and s≥5. Alternatively the direct small-side bound X+s k²/X≤(k−s)+s k²/(k−s) follows by factoring (X−(k−s))(X−s k²/(k−s))≤0, since X≤(1+sqrt(1+4s))k/2≤sk²/(k−s). The extra s+1 accounts for the cut and possible low vertex. See ../../../root/minimum-cut-populations.md.
3. When k>6(s−1), the order must be strictly below both (s+3/2)k+2s+2 and (s+1+3/(s−2))k+2s+3, by ../arbitrary-cut-high-order.md and ../three-common-labels.md. Only the originally proved thresholds are used.
4. If a genuine low minimum-degree vertex lies on a minimum cut, its deficit d=k−δ is ≤s−1 by its two opposite neighbors. A removable vertex followed by universal completion gives n≥(s+2)(k−d−s+1)−1, provided 2(k−d−1)>3s, floor((k−2d−2)/2)+1≥s+1 and 4n<k(k−1). These conservative sufficient conditions include the independent-exterior alternative. The tied case allows d=0; a low avoiding every minimum cut already has input 1's stronger bound. The proofs, including the finite critical-connectivity theorem and exterior-cycle argument, are in ../critical-removable-vertex.md, ../three-common-labels.md and ../../../lowblock/finite-cross-cut-low-degree.md. Uniformly if k≥4s the robust bound is n≥min((s+2)(k−2s+2)−1,ceil(k(k−1)/4)).
5. The maximum degree is at most 3k by ../../../root/effective-cutoff.md. The rooted wedge bounds give n≤3k+1+(k−2)e, and n≤3k+1+e(k−e−1) when 2e≤k−1. See ../../../verify/wedge-order-refinement.md and ../../../verify/wedge-penultimate-matching.md. Write W=ceil((2(n−2k)+ke)/(k+1)). Full column cancellation in ../../../lowblock/active-column-width.md gives W(n−2k−e−2)≤k(k+e) at n>3k+1. This is the linear width. The optional integer strengthening from *two* matched wedges is not used.
6. At a genuine low on a minimum cut, choose high neighbors on opposite sides and let r count their common neighbors. For the smaller wholly high side a, ../../../lowblock/finite-cross-cut-low-degree.md gives 1≤r≤s, d≤r−1, kd≤2k+(k+1)r−n, and
   (r−1)(k−s+1)≤(s+1)k−n+a+s+r(e+s−1).
   Here a≤(n−s)/2, a(n−s−a−k)≤sk² by input 2. Scanning r at the greatest permissible e and a can only increase the worst permissible deficit d. Taking the maximum with zero also admits the tied and low-off-all-cuts cases.

## Finite rectangle without a clique-completion lift

First k<4s²+8s−2. Otherwise the robust nonindependent order in input 4 reaches (s+3/2)k+2s+2 exactly at the boundary k=4s²+8s−2. Its alternative k(k−1)/4 is at least as large, since already at that boundary k−1≥4s+12 and 3k/2≥2s+2. Input 3 applies.

Put x=n/k. One always has x≤9+sqrt((k+1)/3). For x≥9, input 5 and Δ≤3k give
   (x−7)(2x−4+e)≤(k+1)(1+e/k)≤k+1+2e.
The wedge bound gives e≥x−4. Hence
   k+1≥(x−7)(2x−4)+(x−9)e≥3(x−9)².
For x<9 the assertion is immediate.

Suppose s≥100. If k<25s, input 1 and 3s<k give x>2s/3, contradicting 9+sqrt((25s+1)/3)<2s/3 for s≥100 (divide by s; both terms on the left decrease). If k≥25s, input 2 gives x≤2+1/k+25s/24, ruling out 4n≥k(k−1), as (k−1)/4 exceeds this upper bound. Comparing input 4's remaining order with the three-common bound in input 3 gives
   (1−3/(s−2))k<2s²+4s,
so k<2s²+11s (the cross-multiplied surplus is s²−47s>0). But input 1 now gives x>24s/25. At s≥100 the bound 9+sqrt((2s²+11s+1)/3)<24s/25 holds after dividing by s and checking the endpoint 100. This contradiction proves s≤99.

## Exact scalar search

Run the following with Python 3 in this directory. All arithmetic uses integers; no numerical optimizer or graph catalogue is called.

    python3 replay.py > reproduced.tsv
    cmp bands.tsv reproduced.tsv

For each 5≤s≤99 and max(26,3s+1)≤k<4s²+8s−2 the program intersects inputs 1–4. At every fixed n>4k+2 the unrounded width difference in e is concave, hence its minimum on an interval is at an endpoint. The rough excess lower bound in width_possible increases with n, and both positive factors on the left increase with n for every 0≤e≤2k. The relaxed rejection therefore cuts off a final interval of orders. Below 4k+3 the relaxed routine conservatively accepts. The exact test scans degrees for the maximum feasible e using input 5. Its necessary upper cut-deficit bound from input 6 decreases the order range by input 4. No monotonicity of the final, rounded test in n is assumed: the first and last feasible orders are sought separately. Interior gaps may be filled in the published intervals.

The output has 102 inclusive order intervals: 29 at s=5 and 53≤k≤81, 28 at s=6 and 82≤k≤109, 25 at s=7 and 117≤k≤141, and 20 at s=8 and 158≤k≤177. The file records an upper bound cap on each smaller high population for every n in its row. Every row passes the following test.

## Exclusion on each complete interval

Write l for the first order in its interval, h=l−s−1 and C for its recorded cap. For every minimum cut split its two components into high populations X≤Y, with X+Y≥h. The existence of exactly two components when k>6(s−1) is proved in ../../minimum-cut-two-sides.md. The first integer tests, with a=C+1 and b=h−k−a, are b≥k, ab>sk² and b(b−k)>sk². If X≥a and X>b, then X(X−k)>sk²; if a≤X≤b, then X(h−k−X)≥ab>sk². Either case contradicts the cross-product, so X≤C. The accompanying Lean theorem population_bound proves this implication. All 102 rows also give

    l>(s+1)k+2s,   h>sk+C,   C<2k−s,
    h>sk−s(s−1)+(1+1/s)C+1,
    h>sk+k+k/(s−c)−(s−c)(s−c−1)+c+1    for c=1,2.

In particular Y>sk at every minimum cut. By the edge bound of ../../../root/edge-order.md and the first-step argument of ../arbitrary-cut-high-order.md every label of S has a high contact on the smaller side: the displayed order ensures that a cut label adjacent only to a low vertex there shares at least s−1 neighbors with it, hence touches every other label; a path edge decreasing two anchor distances would give an s-root even cover of the large side. A high smaller-side nonport forces all ports to touch just one label. In the private-port case the s representatives each reserve s−1 of their even slots outside the large side. The private representative bound of ../finite-cover-credits.md then gives H=X+Y≤sk−s(s−1)+(1+1/s)X+1, impossible.

All high smaller-side members are thus ports. The Y>sk cover argument forces |U minus T|≤1 for each ordered pair of their supports. By the finite family classification in ../private-five-cut.md the supports on the noncommon labels are singletons (possibly including empty) or co-singletons (possibly including full). In the latter case with d=s−c≥3 the quota bound of ../five-cut-large-degree.md gives Y≤sk. In the singleton case with c=1 or 2 common labels, an opposite contact on a common label gives X≤k. Using the d−1 own-side reserve in ../finite-cover-credits.md gives H≤sk+k+k/d−d(d−1)+c+1, expressly excluded. The c=0 singleton case was private. Thus at every minimum cut there are at least three common labels.

The closing argument is the final separator argument in ../three-common-labels.md. It uses only Y>sk and k>6(s−1) to give a high private opposite contact v on a common label which sees ≥k−s+1 smaller-side vertices, including the adjustment for X=k−s. The boundary of W=N_B[v] has exactly s vertices. More than 2k−s high opposite vertices remain outside W and its boundary. Since C<2k−s, W is the smaller high component of this new cut. But its high v touches just one label, contradicting the three common labels established simultaneously at every minimum cut. This excludes every integer order in the table.

The computational certificate supplies the inclusive sufficient interval domain and the explicit strict integer comparisons. Its graph-theoretic implications use the cited paper arguments. The table can also be read directly from the Lean module for a cross-check.

## Verification boundaries

Graph189FiniteDomain.lean proves the integer population bound for arbitrary cut populations, verifies every recorded terminal inequality on the literal list of 102 bands by kernel reduction, and applies the bound to an arbitrary member of that list. Graph189ScalarReplay.lean translates the rectangular parameter search to Lean, sets an assertion that its complete output equals this literal list including the 102 population caps, and executes that assertion with the Lean evaluator. The standalone Python replay uses a binary order cutoff and forward and backward feasible-order searches; the Lean implementation instead checks each remaining order. The finite-domain boundaries and the graph implications are supplied by the preceding proofs.
