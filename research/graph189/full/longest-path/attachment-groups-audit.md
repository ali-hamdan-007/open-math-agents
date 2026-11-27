# Independent audit of the attachment-group proof

The proof in `attachment-groups.md` is valid under the inherited
degree-three exterior reduction.  It closes the bounded-order
minimum-degree-three branch, including the small values (k=6,7,8,9).

## Counting the groups

On a side of (z) with (s) attachment groups, the outer tail has at
least (M) vertices.  Each of the (s-1) gaps between groups has at
least (M) internal vertices, since the two boundary attachment
positions admit distinct representatives in (H) and (H) is
Hamilton-connected.  Together with the (s) attachment positions, the
side contributes at least (s(M+1)) vertices.  Hence

[
 |Q|ge 1+g(M+1),qquad
 gleleftlfloorrac{3k+1-M}{M+1}ightfloor .
]

Since (kle2M-1), the last bound is strictly below (M).  Some
vertex of (H) therefore labels no singleton group.  All of its
outside neighbors are multiple-contact positions.  Its degree forces
at least (k-M+1) such positions and hence that many groups.  Adding
the (M) omitted vertices gives

[
 nge(M+1)(k-M+2).
]

For (Mle k-2), the right side is minimized at (M=k-2) and equals
(4(k-1)).  This exceeds (3k+2) for every (kge7).

## The two-port clique

If (M=k-1), the group bound gives (gle2), while the degree
argument gives two multiple-contact groups.  Thus there are precisely
two attachment positions (p,q).  Every vertex of (H) must see
both, as well as all other vertices of (H), so (H=K_{k-1}).

Neither port sees (z).  Otherwise (Hsubseteq D_2(z)), and a third
neighbor of (z) missing (H) has degree at most
(1+2+(k-(k-1))=4<k).

Put (C=G-(Hcup{p,q})), so (|C|le2k+1).  The three cases in the
manuscript check at the smallest value (k=6).

* If (C) is disconnected, it has exactly two components, each of
  order at most (k+2) and internal high degree at least (k-2).
  The path-closure threshold is
  (2(k-2)ge k+2), including equality at (k=6).
* If (C) has a cut vertex, its two parts have order at most (k+1).
  No high vertex in a part sees all of (p,q,w), so its internal
  degree is at least (k-2).  The distinct boundary contacts and the
  treatment of the part containing (z) are valid.
* If (C) is 2-connected, a port contact has at most one
  distance-two vertex inside (C), so it has (C)-degree at least
  (|C|-2).  Marker path closure makes all contacts universal and all
  high vertices a clique when (|C|le2k).  At (|C|=2k+1), a
  saturated degree-(k) high noncontact misses at least (k-1)
  other saturated vertices, all at distance two through an original
  contact, and also sees both ports at distance two.  This contradicts
  the cap.  Reversing closure and expanding the marker through
  (p,H,q) is legitimate whether the marker is internal or an
  endpoint.

## The only remaining equality

For (k=6,M=4), the group inequality is an equality with three
multiple-contact positions.  Degree forces (H=K_4) complete to all
three positions.  Equality in the side count puts the innermost
position on each occupied side next to (z).  Thus (Hsubseteq
D_2(z)); every neighbor of (z) must be one of the three positions,
or its degree would be at most (5).

The remaining set (C) has twelve vertices and at most two contacts
to the three positions.  Every component needs two distinct contacts,
so (C) is connected.  A cut vertex would leave two parts of at least
six vertices each inside (C-w), impossible.  Thus (C) is
2-connected.  Contacts have (C)-degree at least ten, noncontacts
have degree at least six, and Dirac gives a Hamilton cycle.  The
displayed prefix in the manuscript uses all of (z), the three
positions and (H), then opens that cycle at a contact.

Consequently the proof establishes traceability throughout the
bounded-order minimum-degree-three branch.  It is a paper proof built
on the previously audited exterior reduction, not an official Lean
verdict and not the unrestricted Graph 189 conjecture.
