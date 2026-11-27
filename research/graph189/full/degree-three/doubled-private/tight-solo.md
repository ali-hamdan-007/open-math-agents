# A solo that avoids the triple-visible remote

Use [the strict support bound](strict-private.md) and the same notation. If |S|+a+2=k+1 and a≥3, **every solo of J is adjacent to t**.

Suppose some solo s avoids t. Its closed remote neighborhood has at least k vertices and lies in H. If t lies in R, it lies in H but outside this neighborhood. The upper bound |H|≤k+1 forces equality and the closed neighborhood is H with t removed. If t lies outside R, the sharper bound |H|≤|S|+a+1=k forces equality and the closed neighborhood equals H. In the latter case t lies outside H. In either case the boundary H outside R has size a+1, consists of nontriple vertices, and every one is adjacent to s.

The missed W, root, two other anchors, and the boundary exhaust J's k positive even-distance slots. Apply the length-four walk and the shortest-path argument of strict-private.md to each **nontriple** remote outside H. Its distance from J is three and it has a neighbor in the boundary. At least c−k−1 such remotes exist in either case, and all are at distance two from s. The anchor, a common middles, and a foreign private via a gate give a+2 more witnesses. Since c≥2k−3 and a≥3, the total is at least k+a−2>k. This contradiction proves the claim.

In particular a lone private with a=3 has |S|=k−4, every nontriple neighbor of t belongs to S, and t is adjacent to every one of its solos. A paired private with a=5 has |S|=k−6 and every one of its solos is adjacent to t. These two tight cases cannot occur at distinct privates: the three solos of the paired private are all outside the lone private's support.

The support geometry is a paper argument. Graph189PrivateSaturation.lean checks conditional metric and counting steps. Workers and reviewers used gpt-6.2-astra and gpt-6.2-sol.
