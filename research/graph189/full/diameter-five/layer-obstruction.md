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

## General bounds on the residual degrees and order

The preceding complete-incidence argument used only the assertion that every anchor is at distance two from every middle vertex. This assertion itself is impossible. Indeed it gives c≤h; every middle vertex v then has at least one far vertex outside its distance-two set, because all a anchors are at distance two and a+f>s. This bounds its D-neighbors by j and gives the same degree contradiction b+c−1+j≤b+d−2<s. Choose v in C missed at distance two by an anchor. All its B-neighbors must be among the anchor's at most i missed B-vertices. Its degree gives
s ≤ i+c−1+d ≤ a+c−1.

Each b₀ in B has at most h neighbors in C, by the cap at an anchor adjacent to b₀. Fix any anchor x. At most h vertices of C are reached from x in two steps. All remaining members of C must have a B-neighbor missed by x, so they belong to the union of the C-neighborhoods of at most i vertices of B. This gives
c ≤ h(i+1) ≤ h(a−h),
where the last inequality follows from i+d≤a and d≥h+1. Therefore
s ≤ a−1+h(a−h) ≤ a−1+floor(a²/4).
This proves a finite, explicit upper bound on the second-smallest degree at fixed minimum degree. As n=1+a+b+c+d+f, b+d≤s, and f=s−h, it also yields n≤1+a+2s+h(a−h)−h.

A second constraint comes from the midpoint cover. A left-type midpoint can see at most l=s−a far vertices at distance two because it already sees all A. A right-type midpoint similarly sees at most h=s−f anchors at distance two. With at most h left centers and l right centers, the cover therefore implies
min(a,f) ≤ h l.
All statements in this section use connectivity alone, once the upstream five_endpoints lemma is available.

## What remains open in this analysis

These inequalities do not exclude all parameter choices. For instance a=20, b=20, c=18, d=14, f=23 and s=34 satisfy the scalar constraints above. A compatible list of sizes does not exhibit a graph or determine traceability. The all-degree diameter-five problem still requires a further structural argument.

There is also an unavoidable gap in middle-layer sizes. Put g=s−b−d≥0. Some middle vertex is missed at distance two by an anchor, as shown above. It has at most i B-neighbors and at most d D-neighbors, forcing c≥l+g+1. By the same degree count, the alternative in which every middle vertex is reached by every far vertex is impossible: it would give c≤l and hence contradict this bound.

Choose a middle vertex missed by some far vertex. It has at most j D-neighbors and at most b B-neighbors. Its degree forces c≥h+g+2. In particular each anchor misses at least g+2 middle vertices at distance two. Each has at least one missed B-neighbor as well.

If some middle vertex is missed both by an anchor and by a far vertex, it has at most i neighbors in B and j in D, so c≥s+1−i−j=l+h+g+2. If no such middle vertex exists, every middle vertex is reached by all anchors or by all far vertices. There are at most h of the first kind and l of the second kind, so c≤h+l. Thus the intermediate values h+l+1 through h+l+g+1 cannot occur.

## A stronger bound using paths inside the first two layers

Every nonadjacent pair x in A and b₀ in B has distance two inside A∪B. Their degrees inside A∪B are at least s−1 and s−h=f respectively. For b₀, this uses its bound of h neighbors in C. For x, only z is an outside neighbor. The degree sum is at least s−1+f > a+b−2, since s>a and f≥b+1. Disjoint internal neighborhoods of two nonadjacent vertices would fit into only a+b−2 places.

Let m be the minimum number of missed B vertices, taken over the anchors. Since c≥h+g+2, no anchor sees every B vertex and m≥1. Every anchor spends at least m positive even-distance slots on B, and f slots on F. It therefore reaches at most h−m vertices of C in two steps. In particular each b₀ in B has at most h−m neighbors in C. Fix an anchor attaining m. The middle vertices outside its distance-two set are covered by the C-neighborhoods of its m missed B-vertices. Consequently

    h+g+2 ≤ c ≤ (m+1)(h−m) ≤ floor((h+1)²/4).

In particular h≥4, since the upper bound is smaller than h+2 for h=1,2,3. Combining h≤a−2 and the degree inequality above gives the sharpened bound

    s ≤ a−1+floor((a−1)²/4).

At a=6 this bounds s by 11. Moreover n=2s+1+a+c−h−g and the lower bounds on c imply n≥2s+max(a+3,f+2). These conclusions again require only the upstream diameter-five endpoint property.

## Exclusion through minimum degree six

The preceding argument already gives a≥6 from 4≤h≤d−1≤a−2, without any assumption of 2-connectivity. Suppose a=6. Then h=4 and d=5. The noncomplete incidence between A and B gives i≥1, whereas i+d≤a, so i=1. Also g=s−b−d=a−i−d=0 and j=d−h−1=0. Each anchor misses some B vertex because c>h, and at most one B vertex because i=1. Thus every anchor misses exactly one, and m=1. Now 6=h+g+2≤c≤(m+1)(h−m)=6, so c=6.

Fix an anchor x and let bₓ be the unique B vertex it misses. At most three of the six C vertices are at distance two from x, since it spends one of its four available places on bₓ. Every C vertex outside those three has a nonempty B-neighborhood confined to the singleton {bₓ}. Thus at least three vertices of C have bₓ as their only B-neighbor. The missing B vertices cannot be the same for every anchor: such a B vertex would have no A-neighbor, contrary to its being in the second layer. Pick two distinct missing B vertices. Their respective groups of at least three uniquely supported C vertices are disjoint and exhaust all six. In particular every middle vertex has exactly one B-neighbor.

A middle vertex with no D-neighbor would have degree at most one B-neighbor plus five peers in C, hence degree at most 6. But s>6 because z is below s. Therefore every C vertex has a D-neighbor. Since j=0, a far vertex has no missing possible neighbor in D or among the other far vertices, so every far vertex sees every D vertex. It follows that each far vertex has all six C vertices at distance two and all six A vertices at distance four. Hence s≥12. On the other hand s≤a+c−1=11, a contradiction.

Consequently every qualifying graph of diameter five has minimum degree at least seven. This is a handwritten conclusion from the upstream endpoint theorem, independent of the published cut-vertex result.

## The endpoint allowance h cannot equal four, at any minimum degree

Suppose h=4. The bounds h+g+2≤c≤(m+1)(h−m) force c=6, g=0, and m equal to one or two. In both cases a middle vertex with exactly one B-neighbor has at least s−6 neighbors in D, since at most five other C vertices and one B vertex can contribute to its degree. Now s−6>d−5=j because s>a≥d+1. Each such singly supported middle vertex is therefore at distance two from every far vertex.

If m=1, pick an anchor missing just b in B. It sees at most three C vertices in two steps, and every remaining C vertex is supported in B only on b. Thus at least three middle vertices are supported only on b. Choose an anchor adjacent to b, as exists by the definition of B. It already sees these three middle vertices in two steps; it spends at least one further slot on its own missed B vertices. Consequently it sees exactly these three middle vertices, misses exactly one B vertex, and the other three C vertices have only that missed vertex as their B-neighbor. All six middle vertices are singly supported and hence at distance two from every far vertex, contradicting c≥l+g+1.

If m=2, each B vertex can support at most two middle vertices, because any incident anchor spends at least two of its four slots on its missed B vertices. An anchor attaining m sees at most two C vertices directly in two steps. Its two missed B vertices must cover the other four C vertices. Equality follows throughout: these two B vertices each support a disjoint pair of the four. Every member of the four is supported only on its own B vertex, since all B vertices seen by the anchor are unavailable to any of the four. All four therefore have distance two from every far vertex, giving l≥4. The degree bound at one of these four vertices also gives s≤d+6, so i+l=s−d≤6, using g=0. Since i≥m=2 this forces i=2 and l=4. Each far vertex now exhausts its even-distance budget on all A and the four singly supported middle vertices. Its distance from every B vertex is at least three and at most four by the high-endpoint theorem, and cannot be four. Each such length-three path must run B–C–D–F, with the intermediate C vertex at distance two from that far vertex. But the only four such C vertices use only the two B supports, whereas b=i+l=6. Contradiction.

Thus h≥5 for all qualifying graphs of diameter five.

## Minimum degree seven

Suppose a=7. Then h=5 as 5≤h≤a−2. This forces d=6, i=1, g=j=0 and m=1. The bounds h+g+2≤c≤(m+1)(h−m) give c=7 or 8. Every anchor misses exactly one B vertex. For each missed B vertex, at least c−4 members of C are supported only on it, since the corresponding anchor has at most four middle vertices at distance two. At least two different B vertices must be missed, as every B vertex has an A-neighbor. Also, j=0 means all F vertices see all D: the middle vertices having distance two from a far vertex are exactly the C vertices with a D-neighbor. Call these the active middle vertices. At least two are active because every A–F pair has a midpoint, whereas a unique midpoint would see all A and F at distance two, exceeding s.

If c=8, two disjoint groups of four singly supported C vertices exhaust C. When s≥9, a singly supported C vertex needs a D-neighbor because all its possible neighbors in B and C number at most eight. Thus all eight are active, which is impossible since c>l. When s=8, the remaining allowance l=s−a=1 permits each far vertex to see at most one active midpoint, also impossible.

If c=7, at least six C vertices are singly supported on two B vertices. Each needs a D-neighbor since s≥8 and the B and C contributions total at most seven. Hence l≥6; the bound s≤a+c−1 gives s≤13. It follows that s=13, l=6, and exactly six middle vertices are at distance two from every far vertex. This exhausts the allowance outside A. As above, each B vertex must be at distance three from any far vertex and therefore must support one of these six C vertices. But these six use only two distinct B supports, whereas b=s−d=7. This contradiction excludes a=7.

Thus every qualifying graph of diameter five has minimum degree at least eight. This is a handwritten assertion from the upstream endpoint theorem and needs no 2-connectivity.

## A strict covering bound for every endpoint allowance

The following general argument gives a shorter proof that h cannot equal four. For a far vertex y let K be the middle vertices at distance two from y. A second-layer vertex not adjacent to any member of K cannot be at distance three from y: each length-three path from B to y must cross C and D in this order. Its distance is at least three and at most four, the latter by the high-endpoint property. It therefore has distance four. The far vertex already counts all A and K at positive even distances, so at most l−|K| vertices of B can be missed by the union of the B-neighborhoods of K. Since b−l=i≥1, this gives

    |N_B(K)| ≥ i+|K|.

In particular it is impossible for every C vertex to have exactly one B-neighbor.

Suppose equality held in c≤(m+1)(h−m). For an anchor attaining m the h−m visible C vertices and the m missed B vertices' respective C-neighborhoods must all have size h−m and be pairwise disjoint. Every hidden middle vertex then has exactly one B-neighbor. Choose one of the m missed B vertices and an anchor adjacent to it. This anchor sees its full block of h−m middle vertices, so it must attain the minimum m and can see no middle vertex outside this block. Repeating the equality argument from this anchor forces every middle vertex outside its visible block to have exactly one B-neighbor, proving that all C are singly supported. This contradicts the far-vertex inequality. Consequently

    h+g+2 ≤ c ≤ (m+1)(h−m)−1 ≤ floor((h+1)²/4)−1.

In particular h≥5, and s≤a−2+floor((a−1)²/4). The order-seven case with h=5 also has c=7 directly by strictness.

More quantitatively, let L consist of the middle vertices at distance two from every anchor. For a minimum-miss anchor x, every member of L lies in its visible group. Each B vertex missed by x is seen by another anchor, which sees all L as well and spends at least m slots on B misses. Hence this B vertex can support at most h−m−|L| middle vertices invisible from x. Thus c≤(m+1)(h−m)−m|L|. In particular, if c≤h+l+g+1 then the earlier middle-layer gap implies L is nonempty: otherwise all C would be seen by F, contrary to c>l.
