# Mixed common-middle degrees among triple-visible remotes

Consider the six high-order degree-three templates of `degree-three-nontriple-cycle.md`. Write R=L₃(z), c=|R|≥2k−1, W for the k−e common middles, with 4≤e≤6 exceptional ports, h for the number of triple-visible remotes, b for the pair-visible remotes' count, Vᵢ for each anchor's visible remotes and f=Σᵢfᵢ for the anchors' expenditure on even witnesses outside R. As established from the templates, fᵢ≥2, f≥7, and f≥8 when a private is doubled.

Let B_H be exactly the triples having at least h+e+1 neighbors in W. Put g=|B_H|, let r=h−g count all other triples, and write K=k−g. If

    k≥2g+7r+84,

then G has a Hamiltonian path. No initial remote connectivity is assumed. For g=0 this is the all-triples theorem, so assume g≥1. We have K−g≥7r+84.

## Fitting a remote cycle or two remote cycles

View R′=R∖B_H as an induced graph. Its order is c−g. Every anchor's visibility in R′ has size at most K−fᵢ, and

    c−g≤3K−f−b−2r.

A vertex of R′ has lost at most g neighbors. Start with F, all nontriple remotes, and select some triples Z from the r other triples. If f+b≥3e+2 select all zero-W triples. Otherwise select just zero-W triples whose supporting ports are all true privates (allowing both twins). In this second case b≤3e+1−f≤12. Let u=|Z|, L=F∪Z induced, and ℓ=|L|. In the first case put s=e. In the second put s=4 when a private is doubled and u>0, and s=3 otherwise, with s=2 when a private is doubled and u=b=0. All L vertices have zero W-neighbors and at most s exceptional neighbors: an exclusive has at most q=1 true private(s) in singleton templates and q=2 in doubled templates, and a pair-visible remote sees at most three exceptionals (a missed anchor misses at most three middles). Consequently

    ℓ≤3K−f−b−3r+u,     δ(L)≥D=K−r+u−s.

Suppose first L is 2-connected. For I⊆L independent of size D+1 we show each pair has a common neighbor in L. If f+b≥3e+2 then 3D−(ℓ+2)≥f+b+2u−3e−2≥0 and the two neighborhoods cannot be disjoint outside I. Otherwise, write sₓ for the number of supporting middles of x. The degree sum of x,y in L is at least 2K−2r+2u−sₓ−sᵧ; its number of available neighbor vertices is at most ℓ−|I|≤2K−2r−f−b+s−1. It suffices that sₓ+sᵧ<f+b+2u−s+1. In a doubled template the left side is at most 4+b+2u, while the right side is at least 5+b+2u since f≥8, s≤4. In a singleton template the left side is at most min(6,2+2b+2u), strictly less than 5+b+2u (use the second bound for b≤2, the first for b≥3). This establishes the common-neighbor claim.

Each x∈I has no neighbor in B_H: otherwise at least h+e+1 W vertices, a visible anchor and D independent peers are disjoint witnesses at distance two, totaling at least k+u+e−s+2>k. Thus its full closed neighborhood in R′ has at least k−s+1 vertices. For any exceptional J supporting x, let Sⱼ′=N(J)∩R′, aⱼ=|N(J)∩W|. Then |Sⱼ′|≤K−2; its remote boundary has size at most e−2+aⱼ, by counting missed W, z, and a missed anchor at J. The aⱼ W-neighbors of J, one anchor and D peers yield aⱼ≤k−D−1=g+r−u+s−1. The closed support neighborhood in R′ contains N_{R′}[x] but the latter misses all other I members supported by J. Hence

    |I∩Sⱼ′|≤1+(K+e−4+aⱼ)−(k−s+1)
             ≤r−u+e+2s−5.

All e supports cover I. This contradicts K≥(e+1)(r−u)+e(e+2s−5)+s, implied by K≥7r+84 and e,s≤6. Thus α(L)≤D.

For an independent triple in L it suffices that the sum of its supporting-port counts be at most f+b+2u−2 to obtain L-degree sum ≥ℓ+2. The large f+b case already has 3D≥ℓ+2. In a doubled template the support sum is at most 6+b+2u and f≥8. In a singleton template use min(9,3+2b+2u). This suffices for b≤2 or f+b+2u≥11. The only remaining possibility is f=7,b=3,u=0. Here ℓ≤3(k−h)−10=3D−1, and failure requires equality and three independent pair-visible vertices each with F-degree D, three supporting ports and all h triples adjacent. In either possible f=7 template its sole double port and the privates of its two anchors i,j constitute the only three supports of a nontriple. All three pair-visible vertices have this support. The remaining anchor has ≤k−h−2 exclusives, so classes i,j contain at least ℓ−3−(k−h−2)=2(k−h)−11 exclusives. Each offending vertex sees all these within two via the two privates, with at most D adjacent. At distance two it therefore has ≥k−h−8 exclusives, ≥h+e+1 W via a B_H-neighbor (g≥1), two visible anchors and both other independent pair-visible vertices. The sum exceeds k. Thus the independent-triple degree sum is at least ℓ+2 throughout, and at least 3D≥3α(L). The Bauer–Morgana–Schmeichel–Veldman criterion gives a Hamilton cycle.

If L is disconnected take its components with j=0. If connected with a cut vertex w, delete w and take its components with j=1. Each part has order ≥D+1−j. We have ℓ≤3D+2: for s=e in the large expenditure case in fact ℓ≤3D−2; otherwise use f≥7 with s≤3 or f≥8,u≥1 with s=4. Thus three components are impossible when j=0. Three parts when j=1 would force ℓ≥3D+1 and f+b+2u≤3s−1. This excludes the large-expenditure case, and gives b+u≤4 since s≤4 and f≥7, while every part has ≥D>4 vertices. Each has at least one exclusive. Here s>q: the only possibility s=q is the doubled case u=b=0,s=2, which already has ℓ≤3D−2 since f≥8. Each exclusive has L-degree at least K−r+u−q≥D+1, so even after deletion each part has order ≥D+1. Three such parts and w exceed 3D+2. Exactly two parts remain.

For either part order m≤ℓ−D−1 and minimum degree ≥D−1 suffice for Hamilton-connectedness whenever ℓ≤3D−2. Otherwise f+b+2u≤3s+1; this is again the small-expenditure case, with at most six nonexclusive vertices per part. Its exclusive vertices have internal degree ≥K−r+u−q−1. This degree, doubled, is at least m+1 because m+1≤2K−2r−f−b+s and f+b+2u≥s+2q+2. For q=1 use f≥7, for q=2,u>0 use f≥8, and for q=2,u=0 use either b≥1 or s=2. An endpoint-marker cycle closure therefore completes all exclusives. There are at most six remaining vertices, all of degree ≥D−1≥77. Their pairs with the m−6 or more completed exclusives can be joined at threshold m+1; each now sees all exclusives. Their remaining pairs qualify either by twice the original minimum degree or because m≥2(D−1)≥13 if that original bound does not suffice. This proves Hamilton-connectedness. Take two disjoint cycles covering L, one per part, including w in a cycle of a part where it has two neighbors by Hamilton-connectedness. Each part contains nontriples since D>u.

For one cycle reserve a unique-class private P and a solo q (there are ≥h+3 exclusive remotes of its class). For two cycles reserve ports P,Q on opposite parts contacted at x,y and incident to distinct anchors a,b. It suffices to use nontriple vertices for this choice: across the two parts the nontriples number at least c−h−1>k−h−2, while any one anchor or exceptional port can see at most k−h−2 nontriples. Thus distinct anchors can be chosen; if their initial choices use the same port, it has two anchor choices and can be paired on the opposite side with any other port touching a nontriple.

## Assigning the vertices outside L

A zero-W triple still outside L and B_H occurs only in the small-expenditure case, and touches a double port J. Its remote neighbor count satisfies |N(J)∩R|≤b+h and hence aⱼ≥k−b−h−e−1=K−b−r−e−1. All these W vertices and three anchors are at distance two from the triple. It has at least K−e−r+1 neighbors on L, so at least

    (K−e−r+1)−(k−aⱼ−3)≥K−g−b−2r−2e+3≥r+e−1

eligible edges on the one or two original L-cycles. An eligible edge has both endpoints adjacent to that triple. The count follows since each successor of a neighbor that is not itself a neighbor has distance two from the triple.

For a remaining triple outside B_H with 1≤a=|N_W(t)|<2r, a W-neighbor misses at most h+2 other W. Thus at least |W|−a−h−2 common middles and three anchors give distance-two witnesses, leaving ≤e+a+h−1 distance-two vertices in L. Its L-neighbor count is at least K−a−e−r+1, giving at least

    K−g−2a−2e−2r+2≥K−g−6r−2e+4≥r+e−1

eligible edges. Each unreserved exceptional J with aⱼ<2(r+e−1) has ≥K−aⱼ−e−r−1 neighbors in L. Its external remote boundary is ≤e−2+aⱼ, giving at least K−5r−6e+7≥r+e−1 eligible original cycle edges. All three inequalities follow from K−g≥7r+84, b≤12 where required, e≤6. Assign distinct eligible edges greedily (there are ≤r+e−1 candidates), and subdivide.

Give each remaining non-B_H triple its own pair of W-neighbors: it has ≥2r and there are at most r such triples. Give disjoint W pairs also to the remaining unreserved exceptional ports: each has ≥2(r+e−1) choices, and at most 2r+2(e−2) have been used prior to the last pair. Choose two distinct W vertices outside all these pairs as the desired endpoints; |W|≥2(r+e−1)+2 follows from the hypothesis.

Consider the induced graph on W, these assigned vertices, and B_H. Adjoin a degree-two marker at the chosen W endpoints. The augmented order N is ≤k+g+r. Original W degrees in this graph are ≥k−3−e−r, since all of B_H is present. Their degree sums reach N because K≥3r+2e+6. Cycle closure completes W, then joins every B_H vertex to all W: their degree is ≥h+e+1 and W degrees are now ≥|W|−1, with sum ≥|W|+h+e≥N. In the closure order the W–assigned vertex–W blocks with the two chosen singleton W endpoints first and last; all unpaired W are singleton blocks. At least |W|−r−e+1=k−r−2e+1 blocks exist, so there are ≥g gaps between blocks because K≥r+2e. Put the g vertices of B_H individually in distinct gaps using their completed W edges. Close the resulting spanning path with the marker, reverse closure and remove the marker. This gives a path through the entire W part with prescribed W endpoints.

With one remote cycle traverse this W path, the four-vertex anchor/z path ending at P's anchor, P,q and the opened expanded remote cycle. With two, traverse the first expanded cycle opened to end at x, then P,a,z,c where c is the third anchor, the W path, then b,Q and the second opened expanded cycle starting at y. All original vertices are covered.
