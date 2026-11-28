# Connectivity at least twice a uniform local degree excess plus one

Let k be the second-smallest degree of a finite connected Graph 189 instance. At each induced u–w–v let e(w) count its positive even-distance vertices. Suppose an integer r≥1 bounds d(w)+e(w)−d(u)−d(v) for every such wedge. Then κ≥2r+1 implies traceability, for every k. Taking r=Δ−δ gives the same connectivity-only criterion in terms of the degree spread. By the rooted L0 result, the hypothesis need only be checked at wedges with endpoints distinct from a fixed root; taking that root at the unique low vertex, if any, also permits r=Δ−k. The zero-excess case follows directly from the L0 threshold at large order and the established n≤3k+2 theorem.

The wedge-order theorem and local Ore Hamiltonicity give traceability at n>(r+3)k+1. For the rooted-hypothesis variant use the rooted L0 spanning-path theorem instead. Work at n≤N=(r+3)k+1. The half-connectivity theorem disposes of k≤4r+3, since floor(k/2)≤2r+1. Assume k≥4r+4, and let h=ceil(k/2). For r=1 and k≥15 use the previously audited moderate-order theorem with κ≥3, valid already at k≥13 with an unrestricted possible low vertex. The finite argument below includes r=1 and k=8 through 14, including its mixed/low cases.

A longest nonspanning P omits a component C with a high vertex by the near-spanning theorem. Take B=C if C is two-connected; otherwise take a terminal block all of whose noncut vertices are high. Let b=|B|. The exterior-degree theorem gives internal degree ≥h to every B vertex except a possible low in whole C or the one cutpoint w in a terminal B. Thus b≥h+1 and B is two-connected. If b≥k, Fan gives an exterior cycle of length d≥k. The standard ℓ=2r+1 disjoint cycle–P connectors give

    n ≥ 3d+ℓ+(ℓ−1)(ceil(d/2)+1) ≥ (r+3)k+4r+1 > N.

Suppose b≤k−1. The degree-two-marker closure on B preserves prescribed spanning paths, and after filling all high/noncut vertices to a clique allows every pair except possibly the two neighbors of its single exceptional vertex of internal degree two. A cycle spans B by Fan. Write a=k−b+1 and L=2r+1. Then there are two lower bounds, uniform for both kinds of B:

    F(b)=(a+2)b+a,                J(b)=(L+2)b+L−(floor(b/2)−1).

For F on a whole C, exclude one high endpoint of its possible bad pair and choose a distinct high vertices, each of which has at least a neighbors on P. There are enough because b≥h+2 for a whole high-containing omitted component and b−2≥a. A cover of fewer than a vertices leaves an uncovered chosen vertex with a surviving contact. Each gap and both tails from the a matched contacts contain ≥b vertices, proving F. For a terminal B, similarly match its high noncut vertices, avoiding one member of the possible bad pair. If b=h+1 the block is a clique, so no additional vertex is excluded and b−1≥a. Otherwise b−2≥a. The remaining R=C−B cannot consist of just the low vertex, since the proved exterior-leaf lemma would give global minimum degree at most two. A high vertex in R has all internal neighbors in R∪{w}, hence |R|≥h. A matched tail can traverse all B to w and then ≥h−1 vertices outside B, using a path from w to a high component of R, with minimum degree ≥h−2 among its high vertices. Compared to the whole-component estimate, F therefore increases strictly by at least 3h−2.

For J, use L distinct contact edges between C and P when C=B by vertex connectivity and König. The possible bad gap is unique and still costs at least ceil(b/2)+1 by the spanning cycle, whence J. For a terminal block, deleting w allows L−1 matched noncut contacts. Losing one mark and gap costs b+1, recovered by the same outside/tail gain ≥3h−2≥b+1. These matchings have enough endpoints since h≥2r+2.

For k≥4r+11 and r≥2, set β=(r+3)/(2r+2). If b≥βk, ignore the full bad gap to obtain n≥(2r+2)b+2r+1>N. If b≤βk, the weaker F(b)≥f(b)=b(k−b+3)−1 suffices. By concavity it is enough to check h+1 and βk. At the first point f(b)≥k²/4+k>N. At βk the difference f(βk)−N equals

    β(1−β)k [k−(4r+6+4/(r−1))]−2.

Here β(1−β)≥5/36, k≥19, and the bracket is ≥1. Thus the difference is positive.

It remains k=4r+c for 4≤c≤10, r≥1. Write b=h+j. For j=1,2,3,4,5 the following rows give a bound proving n>N (an equality means that particular bound only gives n≥N).

| c | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| 4 | F | = | J | J | J |
| 5 | F | F | J | J | J |
| 6 | F | F | F | J | J |
| 7 | F | F | F | J | J |
| 8 | F | F | F | F | J |
| 9 | F | F | F | F | J |
| 10 | F | F | F | F | J |

For fixed c,j both differences F−N, J−N are affine in r since b=2r+ceil(c/2)+j. Substitution at r=1 gives strict positivity for the marked bound and each marked slope is nonnegative. The equality at c=4,j=2 has zero constant and slope. J is increasing in b, so the final column includes every j≥5. The separate elementary check table-check.py verifies exactly these claims.

The equality therefore requires k=4r+4, b=h+2, a=h−1, n=N and B=C (terminal B improves F strictly). Every high C-to-P edge can be prescribed in an a-matching using no bad pair: if one exists, discard its member different from the prescribed high; also discard the possible low from the candidate pool. After fixing the first edge, there are at least b−3≥a−1 available high vertices, each with at least a−1 other path contacts. Match them by the same cover argument. Equality enforces exactly b unmarked vertices in each of the a+1 intervals of every such matching. Thus all high contacts occur at the a indices b+1,2(b+1),...,a(b+1) on P, and every high vertex touches all these marks. Each high C vertex now has all b−1 internal neighbors to reach degree k=(b−1)+a, so the entire C is a clique, even if it contains the unique low vertex. Every low contact belongs to a matching too, by fixing it and using a−1 high vertices for the rest. Therefore precisely these a positions comprise the full set A of C contacts on P. This holds in every rotation realization of P's vertex set.

Consider the rotation family containing P, with endpoints allowed to rotate at either end. The earlier endpoint-growth theorem gives at least k+2 attainable endpoints, hence at least k+1 of them are high. When no low is on P, the weaker elementary k+1 bound suffices: fix the far endpoint and rotate through each neighbor of its high mate. The attainable endpoints never neighbor C. All those adjacent to A are at distance two from a fixed high x in C, so at most k in number. Hence there is an attainable high endpoint e avoiding A. Orient its path starting at e. A pivot neighbor at index p>b+1 would move the old first mark from b+1 to p−(b+1), necessarily a multiple of b+1 by rigidity on the rotated path. Thus every allowable neighbor past the first interval is a mark. The first interval offers only b−1 vertices distinct from e. This gives d(e)≤b−1=h+1<k, a contradiction.

Thus κ≥2r+1 never allows a counterexample under the stated local bound. The result does not assert removal of all low-connectivity cases.
