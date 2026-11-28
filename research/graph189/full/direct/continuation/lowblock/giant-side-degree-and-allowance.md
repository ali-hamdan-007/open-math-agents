# Constant internal-degree loss and a bounded remaining obstruction on a deep giant side

Consider any sequence of hypothetical counterexamples with minimum cut size s tending to infinity. Take a minimum cut S with two sides A,B, where B is the giant, wholly high, and A contains a high nonport and a high neighbor of each anchor. The possible low may lie in A or S. The order, population and width theorems give
    n≥s(k−s+2),   s≤(1+o(1))sqrt(k),   |A|≤(1+o(1))k.
Write P_i=N_A(i), Q_i=N_B(i), p_i=|P_i|, q_i=|Q_i|. A port is adjacent to S and t_v counts its anchor neighbors. For all sufficiently large members of this sequence:
* every A point touches at most four anchors;
* δ(B)≥k−8, every B port sees at least eight outside vertices at positive even distance, and there is no loss when transferring original odd distances in B;
* if B fails to qualify, some B nonport x sees at most seven vertices outside B at positive even distance. Its set I of nearest anchors has 2≤|I|≤6. All but at most 7−|I| high vertices of A touch I. Each i∈I has at least (2−o(1))s B-contacts adjacent to x; some i₀∈I has q_i₀≤(3+o(1))k/s and p_i₀≥k−O(k/s).
In particular if A has at least six high nonports then the whole graph is traceable by minimality and the small-side join in a minimum counterexample. All the estimates except this use of a spanning B path apply without minimizing the counterexample.

The giant side has at most k−s nonports: any high A nonport sees all of them at distance four and its separating second layer has size ≥s. Put
    D=sk−#(ports of B)=Σ_{i∈S}(k−q_i)+Σ_{B ports v}(t_v−1).
Every q_i≤k. From the above three global estimates we get D≤s²−2s+|A|+k≤(3+o(1))k. For any set J of anchor labels the sum of their separate deficits and the repetitions in their Q-union costs at most D; in particular |union Q_j|≥|J|k−D. The Q-sets at any A vertex lie in its positive-even budget. Hence t_a≤1+D/k≤4+o(1), so t_a≤4 for all sufficiently large s.

Write T=4. A high A neighbor of i has at least k−T internal neighbors. Its closed A-neighborhood therefore leaves ≥k−T+1−p_i points of A at distance two from i. Thus
    |R_i|≤p_i+T−1,   R_i=N_B(Q_i)−Q_i.
For y∈Q_i, the members of Q_i outside N_B[y] are at even distance from y along with P_i. Also N_B[y] has ≥k−s+1 members, all in Q_i∪R_i. It follows that
    |Q_i−N_B[y]|≤min(k−p_i, q_i−k+s−1+|R_i|)≤(k+s+T)/2.
For any B vertex y with internal degree below k sum the resulting intersections with N_B[y] over its t_y anchors. Its closed B-neighborhood has ≤k members, so
    t_y(k−s−T)/2 ≤ k + D.
Indeed the Q_i deficits can be included on the right, and the repetitions inside the at most k-member window cost at most the other summand of D. This gives t_y≤8+o(1) and thus t_y≤8 eventually. Since every y was high in G, δ(B)≥k−8.

In fact every p_i≥s−O(1). To prove this it suffices to consider p_i<s. For any anchor l touching a vertex y∈Q_i, N_B[y]⊆Q_i∪R_i, so
    |Q_l∩Q_i|≥(k−s−T)/2−(k−q_l)−|R_i|.
Sum over all such l. The total of |Q_l∩Q_i| is at most |Q_i| plus the global repeated incidences, and |R_i|≤s+T. Since |Q_i|≤k and D≤(3+o(1))k, there are at most 8+o(1) such labels, hence at most eight eventually. The full boundary of Q_i then has at most p_i+T−1+8 members and separates this nonempty set from A. Therefore p_i≥s−11. This proves the claim in either case and supplies ≥8 outside even witnesses for all B ports.

All original B-terminal distances up to three transfer by geodesic-width-and-order.md and the two-step transfer at k≥6s−5. Thus e_B≤k−8 throughout B unless at some B nonport x the outside even count w(x)≤7. Let I be its anchors at distance two; every other high point of A outside P(I)=union P_i has distance four from x, so there are at most 7−|I| such points. The high A nonport is one of them, giving |I|≤6. I cannot be empty as |A|≥k−T+1 from the high A point's internal degree (indeed a nonport has full degree in A). If I={i}, we have p_i≥|A|−7, allowing the possible low. For y∈Q_i∩N(x), its full closed B-neighborhood W=N_B[y] has exterior boundary at most t_y+k−p_i, since each boundary point except its t_y adjacent anchors is a second-layer vertex of y outside P_i. All anchor contacts of y are in I. Since |A|≥k+1 from the high A nonport, the boundary has at most seven members, contrary to s→∞. Hence |I|≥2.

For every i∈I choose y∈Q_i∩N(x) and any high a∈P_i. The ambient path x,y,i,a is geodesic. Its two common-neighbor counts are |N_B(x)∩Q_i| (x has no anchor neighbors) and |N_S(y)∩N_S(a)|≤T. By the high–high geodesic bound their sum is at least 2(n−2k)/(k+1)≥(2−o(1))s. This gives the claimed multiplicity at every i.

Each anchor j outside I has at least s−11 A contacts and therefore shares an A contact with at least one label i(j)∈I, since there are at most eight A points outside P(I) counting any low. Consequently |Q_j∪Q_i(j)|≤k and q_i(j)≤k−q_j+|Q_j∩Q_i(j)|. Sum over j outside I. The deficits give their portion of D, and for any B point incident with I, all its labels outside I can be charged within its t_v−1 duplicate slots. Thus Σ_j q_i(j)≤D, forcing a nearest i₀ with q_i₀≤D/(s−|I|). The degree and even-budget estimates on the two sides give p_i+q_i≥k−T−8+2 (using δ(B)≥k−8), and the final assertion about p_i₀ follows.

There is also an unconditional local Ore condition inside B at every port for large s. All B vertices have e_B≤k; for y∈Q_i, in fact e_B(y)≤k−p_i. The bound on R_i gives d_B(y)≤q_i+p_i+T−2. Therefore d_B(y)+e_B(y)≤2k+T−2. The endpoints of any induced B wedge have internal degree sum at least 2k−16. Since |B|/k tends to infinity, the original wedge order inequality applied to the connected graph B with even cap k forces nonpositive local Ore defect on every wedge centered at a B port. Thus, even without the missing allowance, every obstruction to the rooted local Ore path construction in B has its center at a nonport.

## Completion of the deep wholly-high giant branch

In fact B always qualifies for sufficiently large s under the hypotheses of this note. Thus no sequence of minimum-order counterexample candidates in the inductive argument can leave this deep, wholly-high giant side as an unrouteable smaller instance. More precisely every qualifying graph satisfying these hypotheses for sufficiently large s is either traceable or contains a proper smaller qualifying graph B whose traceability implies that of G.

Because |A|≤(1+o(1))k and all its high vertices have at least k−4 neighbors in A, any two distinct nonadjacent high vertices of A have a common A-neighbor. For any set of labels F⊆S the minimum cut gives |N_A(F)|≥|F|: otherwise removing these contacts together with S outside F separates the surviving A side (|A|>s) from B, using fewer than s points. Thus Hall's theorem gives distinct assigned A contacts of the members of F.

Fix any high a∈A and take F to be anchors neither adjacent to nor within distance two of a. The anchors in S outside N(a) and F give s−t_a−|F| distance-two witnesses. All the assigned A contacts of F are distinct nonneighbors of a, and all but at most one are high, therefore at distance two. Hence a spends at least s−t_a−1 even places in A∪S. In particular at any label i use a high P_i member to give q_i≤K=k−s+5. Replace the previous debit by
    D'=sK−#(ports of B)=Σ_i(K−q_i)+Σ_{B ports v}(t_v−1)=D−s(s−5).
The bound on D now yields D'≤|A|+k+3s≤(2+o(1))k. This use of the Hall witnesses applies at all ratios s²/k.

Suppose B does not qualify. The earlier deduction gives a nonport x with w(x)≤7 and a nearest anchor i₀ whose q₀=o(k), p₀=(1−o(1))k; uniform o(k) terms below may be taken along the sequence. This label alone consumes K−q₀=(1−o(1))k. Consequently
    Σ_{j≠i₀}(K−q_j)+Σ_v(t_v−1) ≤ (1+o(1))k.
Call labels other than i₀ normal here. At every A point the union of its adjacent normal Q sets fits its k even slots. The latest debit bound therefore gives at most two incident normal labels: three would force union at least 3K−(1+o(1))k>k.

Let y be any B point with |N_B[y]|≤k. Its t=t_y is at most eight by the first argument. Write W=N_B[y]. If y touches i₀ then all the Q sets of its adjacent labels have at most k−p₀=o(k) members outside W, because y already sees P₀ at distance two. Their full union therefore has size ≤k+o(k), and tK≤k+o(k)+D'≤(3+o(1))k, giving t≤3.

Otherwise all t labels of y are normal. Let P be the size of the union of their P_j. Their summed sizes are at most 2P since every A member touches at most two normal labels. For each j, its members outside W are at distance two from y along with the whole P-union, so there are at most k−P. Since y has at least k−8 B-neighbors, W⊆Q_j∪R_j and |R_j|≤p_j+3 also gives |Q_j−W|≤p_j+10. Counting misses and repeated incidences yields
    tK ≤ |W| + (1+o(1))k + Σ_j |Q_j−W|
       ≤ (2+o(1))k + min(2P,t(k−P)).
The additive constant 10t is absorbed since t≤8. For 0≤P≤k this minimum is ≤2tk/(t+2). For every integer 4≤t≤8, t>2+2t/(t+2) (already 4>10/3); hence t≤3 here as well. All B points of internal degree below k therefore lose at most three neighbors to S, giving δ(B)≥k−3.

The ports each have at least s−11 outside even witnesses. Any nonport with at most two would, by the earlier argument, see at least two anchors in I as well as the high A nonport at distance four, impossible. Hence all points of B spend three outside even places, and all original B-terminal odd distances transfer. Its positive even cap is at most k−3≤δ(B), contradicting the supposition. Since |A|=(1+o(1))k, the small-side-unprescribed-join.md lemma ensures a spanning path in B suffices to give one in G.
