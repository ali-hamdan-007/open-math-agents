# Traceability at order 3s+3 in diameter five, with a wider window for small D0

Use the notation of diam-five-end-allowances.md and the Hamilton-connected outer blocks U={z}∪A∪B and V=D+∪F from diam-five-outer-blocks.md. Set D0=D−D+, d0=|D0|, T=C∪D0, w=|T|. Write the order as n=3s+3+e with e≥0, so

    c=h+l+g+2+e,       w=c+d0.

Every qualifying diameter-five graph is traceable when e=0. More generally it is traceable whenever e≤g and d0≤h−1; this includes arbitrary orders in this window with d0=0 or d0=1.

## Markers and their expansion

Compress each outer block to a marker, u for U and v for V, on the original graph induced on T. For u the available contacts of x∈T are its neighbors in B; for v they are its neighbors in D+. For each marker include all vertices having at least two contacts, and, separately for each possible contact y, one representative of the vertices whose sole contact is y. These are the marker's only neighbors. Thus any two distinct neighbors of the same marker have a matching to two distinct actual contacts. No uv edge is added. Write J for the resulting graph on w+2 vertices.

At least one v-neighbor exists by a geodesic. The marker u has at least two neighbors. Indeed every C vertex has a B contact. If only one neighbor were selected (and c>1), all the C vertices would have the same sole B contact: a vertex with at least two contacts and any further singleton group would already supply two selections. An anchor adjacent to that one B vertex would see all c>h middle vertices at distance two as well as all f far vertices at distance four, violating the cap.

In both arguments below we use Hamilton-path closure on J at degree-sum threshold w+1, adding only pairs inside T. When T becomes a clique there is a spanning path from u to v, by choosing distinct starting and ending contacts in T. Reverse the closure steps to obtain a spanning path of original J. The markers can have become internal. Replace an internal marker by a Hamilton path of its outer block between the distinct contacts of its two path-neighbors; an endpoint marker requires just one contact and a spanning path beginning at that contact. Since the markers are nonadjacent and their outer blocks are disjoint, both replacements work simultaneously.

## First open order, with D0 unrestricted

If e=0 the strengthened gap c≥h+l+g+2+(i−m)+(j−d0) forces i=m and j=d0. Every far vertex then has all its possible j omissions in D0, so is complete to D+ and to every other far vertex. Hence every productive middle vertex (one with a D+ neighbor) sees all F and is type H. No productive middle vertex sees all A because a+f>s. Also

    w=s−i+1,       |D+|=h+1.

A vertex of D0 must have a D+ neighbor: otherwise its entire degree would be at most w−1, whereas s=w+i−1≥w. Consequently all H vertices together with D0 are at distance two from every far vertex. Let Y be this set, of size at most l. Let X be the C vertices visible at distance two from all A; |X|≤h−m. Write Z for the remaining vertices. Every member of Z is nonproductive, and an anchor missing it at distance two confines its B-neighbors to at most i missed B vertices. All its other neighbors are in T. Because s=w+i−1, it must be adjacent to every other member of T.

The original T-degree of an X vertex is at least s−b=h+1+j+g: it is nonproductive and loses only B neighbors. For a Y vertex the T-degree is at least s−i−|D+|=l+j+g, because any H vertex is missed by an anchor and a D0 vertex has no B neighbors at all. If an X vertex was omitted from u, it has a sole B contact, and its T-degree is at least s−1≥w−1. If a Y vertex was omitted from v, it has a sole D+ contact, and its T-degree is at least s−i−1=w−2. Each vertex in a marked class has degree at least three in J (l≥2); unmarked exceptions have degree at least w−2≥3. All exceptional X or Y vertices can thus be completed to T at threshold w+1. Each marked X–marked Y pair meets the same threshold since its degree sum is at least

    (h+2+j+g)+(l+1+j+g) ≥ w+1.

Now take any of the remaining class vertices in a class of size t. It has degree at least w−t+1 from all original vertices outside the class and its marker. Its initial marked degree was at least t+1, since |X|≤h−m and |Y|≤l. Twice the larger of t+1 and w−t+1 is at least w+1. All remaining original pairs thus close, proving the assertion at n=3s+3.

## General criterion and the d0≤1 window

At any e≥0, let X be the u-marked C vertices visible from all A. Let Y be the v-marked type-H middle vertices and v-marked D0 vertices. The two sets are disjoint since a+f>s. All remaining originals form Z. The following are lower bounds for their degrees in J:

    rX=h+g+2,    rY=l+g+d0+1,    rZ=s−max(i,j)−1.

For X, B accounts for at most b neighbors; since some far vertex misses an X vertex at distance two, it has at most j D+ contacts, as all its D+ neighbors are omitted by that far vertex. Its left marker adds one. For Y there are at most i B neighbors (none for D0) and at most d−d0 D+ neighbors, and its right marker adds one. For Z, an unmarked all-A-visible C vertex has one B contact and at most j D+ contacts. A type H omitted by v has at most i B contacts and exactly one D+ contact. A middle vertex visible from neither whole endpoint layer is nonproductive by the midpoint theorem, so loses at most i B neighbors. A D0 vertex not marked by v loses at most one neighbor in D+. These cases justify the stated rZ.

A numerical criterion valid at any order with e≥0 is

    rX+rY ≥ w+1,       rZ+min(rX,rY,rZ) ≥ w+1.                (3)

The second inequality completes all Z vertices to all originals. The first completes all X–Y pairs. Now |X|≤h−m and |Y|≤l+d0 (there are at most l type-H midpoints). Each marked class again has both degree bounds t+1 and w−t+1, where t is its size, and the closure and expansion prove traceability.

When 0≤e≤g and d0≤h−1, the first inequality holds because rX+rY−(w+1)=g−e. For the second, rZ≥h+l+g follows from s=i+h+1+j+g+l. Each of rX,rY,rZ is at least e+d0+3 by l≥2, e≤g and d0≤h−1. Their stated sum reaches h+l+g+e+d0+3=w+1. This proves the wider window, including both requested small values of d0.
