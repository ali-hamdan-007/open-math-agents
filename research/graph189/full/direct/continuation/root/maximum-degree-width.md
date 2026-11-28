# The full conjecture reduces to finitely many graphs

Under the documented Graph 189 hypotheses there are only finitely many possible counterexamples up to isomorphism. Every graph of sufficiently large order satisfies the conjecture. This argument does not exclude all smaller graphs or give a proof of the exact parent in Lean.

**A finite inequality at the maximum degree.** Let n be graph order, k second-smallest degree, Δ largest degree, m=n−2k, e=Δ−k. In any counterexample with n≥Δ+k+2,

    (m−e−2)(2m+ke) ≤ k(k+1)(2k+e),       n ≤ 3k+1+(k−2)e.

The second inequality also holds for smaller n in the residual degree range. Choose a root x of degree Δ. For each high y at distance three choose a geodesic x,i,j,y, and write D=|N(x)∩N(j)|+|N(y)∩N(i)|. The summed two-wedge inequality of ../lowblock/geodesic-width-and-order.md, retaining the endpoint degrees and writing E(v) for the positive-even count, reads

    (k+1)D ≥ 2(n−2k) + k(d(x)+d(y)−E(i)−E(j)) ≥ 2m+ke.

At least n−Δ−k−2=m−e−2 high vertices are at distance three: the root, first layer, all positive even layers and the possible low exception account for the rest, since high vertices have mutual distance at most four. Summing the first part of D over these y uses at most Δk incidences because all its witnesses are first neighbors of x seeing y at distance two. Summing the second part uses at most k²: its witnesses lie in the second layer of x, and the y adjacent to any single such witness all have distance two from one fixed predecessor of that witness. This proves the first formula. For the second, prescribe a minimum-degree vertex as the root for the rooted local Ore theorem. Every induced wedge with its endpoints different from this root has both endpoints of degree ≥k. Its degree excess (center degree plus center even count minus the two endpoint degrees) is at most Δ−k. The penultimate inequality and rooted Ore criterion in ../verify/wedge-order-refinement.md and trimmed-high-degrees.md now prove the asserted order restriction. This step permits one arbitrarily low vertex.

**An absolute gap in the leading order constant.** On any hypothetical sequence with k increasing without bound,

    limsup n/k^(3/2) ≤ sqrt(2/3).

Indeed the known order ceiling gives n=O(k^(3/2)), and we need only subsequences with n/k^(3/2) bounded below by a positive constant. The general adjacent-degree estimate gives Δ≤5k, so m−e−2=(1−o(1))n. The first finite inequality then gives e=O(k²/n)=O(sqrt(k)). Thus 2k+e=(2+o(1))k. The second finite inequality implies ke≥n−3k−1. Substitution into the first gives (3−o(1))n²≤(2+o(1))k³, as claimed.

**Finiteness.** If there were infinitely many nonisomorphic counterexamples, their orders would be unbounded, and the previous order ceiling would force k to grow along a subsequence. The traceability theorem at every fixed connectivity s, for example k≥6s²+10s−6 with s≥5, and the unconditional s≤4 result then imply s grows along a further subsequence. The bounded intersection of opposite anchor supports and the absolute order lower and upper in ../verify/common-anchor-intersections.md force s²/k→1 and n/k^(3/2)→1 on this subsequence. This contradicts sqrt(2/3)<1. The deductions leading to that necessary limit use the earlier degree-independent order ceiling and are independent of the stronger estimate here.

The remaining task is to exclude the bounded exceptional range or find an example in it. All k≤25 are independently covered in ../sep/cover/five-through-25.md and the connectivity-at-most-four results.
