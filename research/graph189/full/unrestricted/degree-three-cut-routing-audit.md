# Independent audit of the degree-three complement cut lemmas

This audit covers the proved component-count, remote-distance, closure and
gluing statements in degree-three-complement-cut.md and
degree-three-two-arm-routing.md. It does not endorse the cases explicitly
left open there.

## At most two components

The proof that C-w has at most two components for k>=10 is sound. If one
anchor touches three components, a chosen anchor-neighbor in each component
has at most four neighbors outside it: w and the three anchors. Its closed
internal neighborhood therefore has at least k-3 vertices. The three closed
neighborhoods are disjoint and lie in the disjoint union of T and the
anchor's exact distance-two set. Thus 3(k-3)<=2k, impossible for k>=10.

For three arbitrary components, at most six anchor-component incidences
occur. With the manuscript's notation, the witnesses through w give

    2b <= 3(k-1).

The closed internal neighborhood of x_i has at least k-s_i vertices. After
removing its at most a_i members adjacent to w, the rest are exact
distance-two witnesses from w. The three sets are disjoint. Since w has an
even-distance witness outside C,

    3k - sum(s_i) - b <= k-1.

Together these imply k+5<=2 sum(s_i)<=12, contradicting k>=10.

## Remote distances

For remotes x,y in different components of C-w, every anchor-using path has
length at least four and every C-path uses w. The high-pair distance bound
supplies a path of length at most four. Hence

    d_G(x,y)=min(4,d_C(x,w)+d_C(y,w)).

The only odd possibility is the pair of depths 1 and 2. If x has depth at
least three, a shortest path inside its component to a neighbor of w gives
an exact internal distance-two witness. Together with the always-available
witness in {z} union A, at most k-2 remotes lie outside x's component. At
n>3k+2 there are at least 2k-2 remotes after w is excluded. Two deep
components would force at most 2k-4 in total. Thus there is at most one deep
component, and it contains at least k remotes.

## Two-arm splice

Every component of C-w has a w-contact and a port. For k>=7 its order is at
least k-3>1, so 2-connectivity makes those roles available at distinct
vertices. Each part therefore has a usable anchor. If the two usable-anchor
sets admitted no distinct choices, both would be the same singleton. Any
other anchor would then have at most one neighbor in each part, and at most
six neighbors total after adding z, w and the other anchors, contrary to
degree at least k. Distinct usable anchors b,c exist. The splice

    a,z,b, then a D-path to w, then an E-path ending at c

uses disjoint vertices and original edges. The one-ended variant when the
anchor triple contains an edge is also correct.

## Closure thresholds

In a part of order m with p ports, remotes have internal degree at least
k-1 and ports at least k-4. A leaf at a prescribed start gives threshold m;
a degree-two endpoint marker gives threshold m+1. Write these as m+e for
e=0,1.

If m+e<=2(k-4), all original vertices complete immediately. Under

    m+e<=2(k-1),  p<=k-5-e,

the remotes first complete. A completed remote has degree at least m-p-1,
so its sum with a port is at least m-p-1+k-4>=m+e, completing every
remote-port edge. Failure of the first range implies m+e>=2k-7; combined
with the port bound this gives 2(m-p)>=m+e, completing the ports. Reversing
closure preserves the original leaf or marker edges, hence the prescribed
start or endpoint pair.

For a part opposite a deep remote component, the sharper order bound

    |D| <= 2k-2-d-p_E-j

substitutes correctly into the closure criterion. It proves the stated
p_D<=k-6 Hamilton-connected case and p_D<=k-5 arbitrary-start case. The
failure lower bounds on order, remotes and remaining port deficit also have
the claimed integer endpoints.

No gap was found in these proved criteria. They leave open the two cases the
manuscripts identify: two shallow remote arms, and a large arm beyond the
displayed closure ranges.
