# Degree-five root: parameters and the saturated two-port case

Let z be the unique vertex of degree five, let k be the second-smallest
degree, and suppose n>3k+2. Assume k>=7 and G-N[z] is disconnected. By the
remote-component lemma there are exactly two components. Write K for the
component contained in T=N2(z), D for the remote-bearing component, P for its
ports, r=|K|, s=|P|, and C=D-P.

Put a=k-r. Then

    2 <= s <= a <= 4,
    r+s <= k,
    |C| >= 2k+a-s-3.

Every K vertex has at least a+1 neighbors among the five anchors N(z), since
it has no neighbor outside K union N(z). The number of vertices at distance
four from z is at most a-s. These give the six possible parameter pairs

    (a,s)=(2,2),(3,2),(3,3),(4,2),(4,3),(4,4).

The saturated pair (a,s)=(2,2) is always traceable.

Indeed, here |K|=k-2 and |T|=k, so there is no fourth layer. Write u,v for
the two ports. Every member of C is adjacent to u or v. No anchor touches
both ports: such an anchor would see all of C at distance two, but
|C|>=2k-3>k. Thus the nonempty anchor-neighborhoods of u and v are disjoint.

For an anchor alpha touching u, every member of N(u) intersect C lies at
distance two from alpha. There is one further even-distance witness. If
alpha misses another anchor, that anchor is two steps away through z. If
alpha is complete to the other anchors, then v is two steps away through an
anchor touching v. Hence

    |N(u) intersect C| <= k-1,
    |N(v) intersect C| <= k-1,

and |C|<=2k-2. Thus |D|<=2k.

Add a marker b adjacent only to u and v. In D+b the Hamilton-path closure
threshold is |D|. Every member of C has degree at least k in D, so closure
makes C a clique. Each port has a neighbor in C, and their C-neighborhoods
have union of size at least two; otherwise deleting the other port, or their
sole common C-neighbor, would disconnect G. Choose distinct x in N(u)∩C and
y in N(v)∩C. The closed graph has the spanning path

    b,u,x, then all remaining C vertices, then y,v.

Reversing path closure gives some spanning path in the original marked graph.
The displayed endpoints need not be preserved, which is harmless in the
expansion below.

It remains to route the shell S=G[A union {z} union K] between prescribed
distinct anchors. Add a degree-two marker at those anchors. This auxiliary
graph has k+5 vertices. A K vertex has degree at least k in the shell. An
anchor loses at most the two D ports, so its shell degree is at least k-2.
For k>=7, k+(k-2)>=k+5. Cycle closure therefore makes every anchor complete
to K and makes K a clique, without changing marker or z edges. To display a
Hamilton cycle through the marker b, call its prescribed anchors a1,a2 and
the others a3,a4,a5. Choose distinct x1,x2,x3 in K and use

    b,a1,x1,a3,x2,a4,z,a5,x3,
    then every unused K vertex, then a2,b.

All displayed edges exist in the closed shell. Reverse closure and delete
the marker to obtain the prescribed anchor-to-anchor spanning path.

In the original D+b path, if b is internal then its two path-neighbors are
u and v. Replace the subpath u,b,v by u, an anchor touched by u, a shell path
between that anchor and a distinct anchor touched by v, and v. The anchor
sets are disjoint, so the endpoints are distinct. If b is an endpoint next
to one port, say u, choose any anchor touched by u and any different anchor;
replace the initial edge b,u by a shell path ending at the chosen u-anchor,
then u. The shell theorem allows any prescribed distinct anchor endpoints.
This produces a spanning path of G in every marker position.

Consequently a disconnected counterexample with a unique degree-five root
must have one of

    (a,s)=(3,2),(3,3),(4,2),(4,3),(4,4).

The two-port cases narrow further. For s=2, let F be the fourth layer and R
the third layer. Then |F|<=a-2 and R=N_C(u) union N_C(v). The lower bound on
C gives |R|>=2k-3, so a common anchor of u and v is impossible: it would see
all of R at distance two. The same anchor argument as above yields
|N_C(u)|,|N_C(v)|<=k-1, and therefore

    |R|<=2k-2,       |D|<=2k+a-2.

Whenever |D|<=2k, the preceding marker proof applies unchanged. Thus

* at (a,s)=(3,2), only the extreme |D|=2k+1 remains. It has one fourth-layer
  vertex, disjoint sets N_C(u),N_C(v) of size k-1, and no other third-layer
  vertices;
* at (a,s)=(4,2), only |D|=2k+1 or 2k+2 remains, with at most two
  fourth-layer vertices.

The apparent (3,2) extreme is also traceable for k>=12. Let U and V be the
two disjoint layer-three port-neighborhoods, each of order k-1, and let f be
the sole layer-four vertex. The vertex f has a neighbor in each of U,V:
either side alone has only k-1 vertices, fewer than its required degree k.

The shell argument remains valid when |K|=k-3. With the endpoint marker its
order is k+4. A K vertex has shell degree at least k, while an anchor has
shell degree at least k-2, so every missing anchor-K edge meets the cycle
closure threshold already for k>=6. The same explicit marker cycle therefore
gives a spanning shell path between arbitrary distinct anchors.

Choose an anchor alpha touching u. Its only possible neighbors are z, four
other anchors, u, and K. Since its degree is at least k and the port anchor
sets are disjoint, alpha has at least k-6 neighbors in K. These vertices,
z, and f are distinct distance-two witnesses from u. If Y is the set of
vertices of V incident with a cross edge from U, then Y is also at distance
two from u. The cap gives |Y|<=4. Symmetrically at most four U vertices are
endpoints of cross edges from V.

Every x in U has neighbors outside U only among u, f and Y. Therefore

    degree_U(x) >= k-6.

The same holds in V. For k>=12, a graph on k-1 vertices of minimum degree
k-6 is Hamilton-connected: after adding a degree-two endpoint marker, the
degree-sum threshold is 2(k-6)>=k. Choose x in N(f)∩U and y in N(f)∩V.
Take a spanning U-path from any other vertex to x, cross through f to y,
and take a spanning V-path from y to any other vertex. Prepending u and
appending v gives a u-v Hamilton path of D. The shell expansion above then
spans G.

Thus (a,s)=(3,2) is closed for k>=12. The cases k=7,...,11 in that single
extreme remain.

One subcase of (a,s)=(4,2) closes the same way. If |D|=2k+1 and there is
exactly one fourth-layer vertex f, then the layer-three sets U,V are disjoint
and each has order k-1. Since K is now complete to all five anchors, each
port counts K, z and f among its distance-two witnesses. Only two opposite
cross-edge endpoints remain possible. Hence every vertex of U and V has
internal degree at least k-4. These two graphs are Hamilton-connected for
k>=8, and u-U-f-V-v spans D. The shell expansion finishes G.

The (4,2) cases with two fourth-layer vertices, the small (3,2) extremes,
and the three/four-port parameter pairs still need separate treatment.
