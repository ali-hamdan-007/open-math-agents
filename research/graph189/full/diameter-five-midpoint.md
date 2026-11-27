# Endpoint and middle obstructions in diameter five

Let G be finite, simple, connected, and of diameter five. Let s be its second-smallest degree. Assume at most s vertices have positive even distance from each vertex. The upstream theorem five_endpoints then implies that every distance-five pair contains the unique below-s vertex z. Number the five layers from z as A,B,C,D,F, with sizes a,b,c,d,f. The graph outside z has all degrees at least s.

The following inequalities do not require 2-connectivity. The cap at z gives b+d ≤ s. Each vertex in A has at most a+b possible neighbors, so s ≤ a+b. Each far vertex has at most d+f−1 possible neighbors, so s ≤ d+f−1. Thus d ≤ a and a+f ≥ s+1. For all x in A and y in F, their distance is at least four by the triangle inequality. Both have degree at least s, so they cannot be distance five and consequently have distance four. Every such shortest path crosses C at distance two from x and from y.

Write h = s−f and j = d+f−1−s. Then h ≥ 1, since each x in A has all F at distance four and at least one vertex of C at distance two. Every y in F misses at most j vertices in D and the other vertices of F together.

**The incidence between A and B cannot be complete.** If it were, every middle vertex in C would be at distance two from every vertex of A since it has a B-neighbor. The cap at any x in A gives c ≤ h. Fix any v in C. If v had more than j neighbors in D, each y in F would meet at least one, so all F would be at distance two from v along with all A, contradicting a+f ≥ s+1. Consequently v has at most j neighbors in D. Its total degree is at most b+c−1+j ≤ b+h−1+j = b+d−2 < s. This is impossible. In particular s ≤ a+b−1 and d ≤ a−1.

**The far set has size at most s−2.** If h=1, each vertex of A has all F at distance four plus one C at distance two. This exhausts its cap. The vertices of A form a clique since any missing pair is at distance two via z. Any missed B vertex has a neighbor in A and hence would be at distance two through that clique. Thus A is joined to all B, which was just excluded. Therefore h ≥ 2. Now d ≥ h+1 ≥ 3, and a ≥ d+1 ≥ 4. These deductions, including the minimum-degree bound a ≥ 4, use connectivity alone.

More generally, put i = a+b−s. Each vertex of A misses at most i vertices among A minus itself and B. For any v in C, if v has more than i neighbors in B, all A reach v in two steps, so v must have at most j neighbors in D. Thus each v in C satisfies at least one of the bounds deg_B(v) ≤ i or deg_D(v) ≤ j. The remaining case allows holes on both sides of the middle.

The published connectivity and order hypotheses are in Easwar–Johari, arXiv:2609.11719, Theorem B. They cover graphs that are not 2-connected and orders at most 2s+3. The counting above is independent of these results.

## Every geodesic midpoint reaches an entire end layer in two steps

Let i=a+b−s, j=d+f−1−s, h=s−f, and l=s−a. Consider any v in C lying on a shortest z–F path. There are vertices b₀ in B and d₀ in D adjacent to v, and d₀ has a neighbor in F. Every such b₀ has at most h neighbors in C because any A-neighbor of b₀ sees all F at distance four as well as those C-neighbors at distance two. Likewise d₀ has at most l neighbors in C because any F-neighbor sees all A at distance four.

Write p and q for the numbers of neighbors of v in B and D respectively. The closed neighborhood of b₀ contains at least s+1 vertices, all in A,B,C. At least s+1−h=f+1 of these are in A or B. At most p of these are adjacent to v, and all the others are at distance two via b₀. The closed neighborhood of d₀ supplies, by the same argument, at least s+1−l−q=a+1−q additional vertices at distance two from v in D or F. Consequently p+q ≥ a+f−s+2. But i+j=a+f−s−1−(s−b−d) ≤ a+f−s−1, so p>i or q>j. The first inequality forces every vertex of A to reach v at distance two, since each anchor misses at most i of B. The second inequality similarly forces all F to reach v at distance two. Both cannot occur since a+f>s. In fact one of the following mutually exclusive alternatives holds.

* All A reach v in two steps, some F does not, q≤j, and p≥i+3+(s−b−d).
* All F reach v in two steps, some A does not, p≤i, and q≥j+3+(s−b−d).

Call the respective sets of geodesic midpoints L and H. Every pair A×F has a midpoint, so its set of middle witnesses is covered by the rectangles A×Fᵥ for v in L, and Aᵥ×F for v in H, where Aᵥ,Fᵥ are the endpoints at distance two. In particular, either every far vertex is seen from some member of L, or every anchor is seen from some member of H. If neither held, the pair made from the two uncovered endpoints could not have a midpoint. Finally |L|≤h and |H|≤l since each anchor sees all L and each far vertex sees all H, in addition to the opposite end layer.
