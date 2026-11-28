# Private opposite ports on a common label

Let A,B be the sides of a minimum separator S. Let C consist of c≥3 common labels touched by every high A vertex, and let D=S∖C, with d=|D|≥2. For each i∈D choose a high A representative aᵢ touching i. Assume each high A vertex has at most one label in D. Thus aᵢ touches exactly C∪{i}. Let X,Y count the high vertices of A,B respectively, and let k be the second-smallest degree.

Assume there is no high B port whose only label belongs to C. The following rows cover every high B vertex twice.

- Count the positive-even row of each aᵢ twice. Every B port touching j∈D is at distance two from aⱼ, and every B port touching C is at distance two from every representative. Thus these rows pay twice for each port.
- Count each label's exact-distance-two row once. A high B nonport with at least two such labels is paid twice by these rows.
- A remaining high B nonport y has at most one label at distance two. If that label were in C, the high-private-predecessor lemma would give a forbidden high private port at the label. Thus no label in C is at distance two, and since d≥2 some i∈D is also missing at distance two. Every high-to-high distance is at most four. An odd distance from aᵢ to y would have to be three and would meet a label touched by aᵢ at distance two from y. All labels touched by aᵢ lie in C∪{i}, so the row of aᵢ pays twice.

The common rows cost at most ck, and the two copies of all representative rows cost at most 2dk. The sum of all remaining rows is at most X+d(c+1) by the residual-label neighborhood count. Hence

    2Y ≤ (2d+c)k + X + d(c+1).

An opposite contact on any common label sees all high A vertices at distance two, giving X≤k. If k≥2d then (c−1)k≥2d(c−1)≥d(c+1). Consequently Y≤(d+c)k=sk. Whenever Y>sk this proves existence of a high private B port at a common label. The argument applies with the possible low vertex anywhere. In particular it covers every terminal band satisfying the residual-singleton classification.

Graph189ResidualDoubleCharge.lean contains the finite incidence sum. Graph189ResidualPrivatePort.lean supplies its original-graph geometric cover. Graph189ResidualPrivateExists.lean combines that cover with the trimmed residual row bound and returns a high private port on a common label as required for the second cut.

## Refinement with the minimum-cut boundary debit

Each representative has exactly c+1 neighbors on S. Applying the minimum-cut boundary debit to its high B even row bounds that row by k+1−d. Repeating the same count gives

    2Y ≤ 2d(k+1−d) + ck + X + d(c+1).

For c≥1, d≥2 and k≥d this is at most 2sk. Indeed X≤k and d(c+3−2d)≤d(c−1)≤k(c−1). Thus the high private B port exists even with just one common label in the residual-singleton case.

There is a second use of the same boundary debit with the two sides interchanged. Once b is private on a common label i, every high A member is at distance two from b and its support has size one. Therefore X+s≤k+1. On the other hand a high a in A has degree at most |A|−1+|supp(a)|≤X+|supp(a)|. So every high A member touches at least s−1 labels. This derives uniform two-contact support at s≥3 from existence of a high B private contact on a common label at each cut. For the full high A branch, the prescribed-label result supplies that contact. These refinements are paper deductions; the main Lean interface above retains the c≥3 terminal hypothesis.

## The zero-core test

At c=0 the singleton-family quota is Y≤sk−s(s−1)+X/s+1. In particular Y>sk implies X>s²(s−1)−s. The 113 terminal rows have maximal Xcap equal to 91, 119, 152 and 189 at s=5,6,7,8 respectively. The corresponding thresholds are 95, 174, 287 and 440. Thus the finite table already excludes the zero core. On a positive core the boundary refinement above then forces the uniform lower bound s−1 on the support of every smaller-side high vertex. This provides an alternative to excluding core sizes one and two by their own terminal quota inequalities.

The full singleton-family quota has an equivalent direct count, also useful at c=0. Each high B vertex either lies in one positive-even representative row, is at distance two from some common label, or is at distance two from every residual label. For the last alternative, a missed residual label would force even distance from its representative. Giving each representative row and each common-anchor row weight d and each residual exact-two row weight one yields

    dY ≤ d²(k+1−d) + dck + Q_D,

where Q_D≤X+d(c+1). No subdivision of the B ports into support classes is needed.

For a whole range of orders one can obtain the zero-core test from the product inequality. Write H=X+Y and assume s≥5. If Y≤sk, put t=Y/k. For t≤(1+√(1+4s))/2 one has H/k≤2t≤s+1. Above this turning point, XY≤kX+sk² gives H/k≤t+s/(t−1). This convex function reaches its maximum on the interval up to s at an endpoint, giving H/k≤s+s/(s−1). Consequently H>(s+s/(s−1))k forces Y>sk, then X<sk/(s−1). If k≤(s−1)(s²−s−1), this gives X≤s²(s−1)−s automatically. These sufficient inequalities use the same geometric prerequisites on minimum cuts and the same lower-endpoint argument as the terminal proof.

## Lean verification

The four source modules Graph189ResidualDoubleCharge, Graph189ResidualPrivatePort, Graph189ResidualPrivateExists and Graph189ResidualTerminal passed the pinned compiler with warnings treated as errors. Its axiom reports contain propext, Classical.choice and Quot.sound. The main theorems are Graph189ResidualPrivatePort.private_exists and Graph189ResidualPrivatePort.terminal_of_missing_label. The latter applies the recut theorem to the original graph using a high A vertex missing some label, and proves the entire residual-singleton contradiction under the uniform two-support hypothesis. Its log is residual-terminal.log. The rebuilt-from-source entry point is replay-residual-private.sh with OMA_FC set to the pinned, built project.
