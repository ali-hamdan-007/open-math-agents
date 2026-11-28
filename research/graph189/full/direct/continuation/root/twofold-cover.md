# Two even-distance budgets at each separator label

Let S be a vertex separator with sides A and B. Let Y be high vertices on the B side. Suppose D⊆S has at least three labels and that, for each i∈D, there is a high A vertex xᵢ adjacent to all of S except i. We may include every high vertex of B in Y. Then |Y|≤|S|k. This is the co-singleton alternative in the terminal proof.

Use two lists of witnesses, each indexed by S. On the first list put the separator vertices themselves. On the second list replace each i∈D by xᵢ, retaining the other labels. None of these witnesses belongs to Y, so each list entry sees at most k vertices of Y at even distance. Counting a vertex twice from two distinct list positions is permitted.

Every y∈Y is seen at least twice. If y has a separator neighbor j, each representative xᵢ with i≠j sees y at distance two through j. There are at least two such i in D.

Suppose y has no separator neighbor. For every xᵢ its distance to y is at most four by the high-pair diameter bound. An odd distance must therefore be three. Any such geodesic crosses S at a neighbor of xᵢ whose distance from y is two. Let E be the labels in S at even distance from y. If |E|≥2, the first list suffices. If E is empty, odd distance is impossible for any xᵢ, so at least two positions of the second list suffice. Finally suppose E={j}. If j lies outside D, the two copies of j suffice. If j∈D, an odd geodesic from xⱼ would have to go first to j, its single missing label. Therefore xⱼ and j both see y. This proves the twofold covering claim, giving 2|Y|≤2|S|k.

Together with the actual cut support classification, this yields a convenient dichotomy at the terminal orders where |Y|>|S|k. Either every small-side high vertex uses at most one label outside their common labels, or at most two separator labels are noncommon. For the second implication, every label has a high A contact at these orders. A missing label i can then be represented by a high A vertex missing only i. Three noncommon labels would give the twofold cover above.
