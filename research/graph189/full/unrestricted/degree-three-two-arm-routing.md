# Routing through a cut of the connected degree-three complement

Use the hypotheses and notation of `degree-three-complement-cut.md`. Write A=N(z), T=N₂(z), C=G−N[z], R=V(C)∖T. Suppose a cut vertex w of C leaves exactly two components D,E. A vertex in T is a port. Every component of C−w contains a neighbor of w and a port: use connectedness of C for the former, and connectedness of G−w for the latter. Its vertices with neighbors in A∪{w} are at least two distinct vertices. A component has order at least k−3 by high degree and the four possible outside neighbors; when k≥7 it has more than one vertex. Deleting a sole boundary vertex would then disconnect G.

**Routing criterion for k≥7.** In a part D, call an anchor a usable when there are distinct u,v∈D with au and wv edges. The set of usable anchors is nonempty by the preceding boundary property. Distinct usable anchors b,c may be chosen in D,E, respectively. Otherwise both usable sets equal the same singleton; take any other anchor j. In each part j has at most one neighbor, as two neighbors allow a contact different from any chosen neighbor of w. Its degree is at most two in the parts, one at w, one at z and two in A, totaling six.

Consequently, if each part is Hamilton-connected, G is traceable. With a the third anchor, traverse a,z,b; span D from its b-contact to its distinct w-contact, traverse w, then span E from its w-contact to its distinct c-contact, and end at c. No edge between anchors is needed.

There is an additional one-ended criterion when A has any edge. The four vertices A∪{z} have a spanning path ending at any prescribed anchor b. If the other two anchors are adjacent, use that edge followed by z,b. Otherwise b belongs to an anchor edge, and one can start at the anchor outside that edge, proceed to z, and traverse that edge ending at b. Hence it suffices in one part to have a spanning path between a usable anchor contact and a distinct w-contact; in the second only a spanning path beginning at a neighbor of w is required. In particular one Hamilton-connected part and one part traceable from every start suffice.

**A closure criterion for part size and port count.** In a part L of order m let p=|T∩L|. Every remote has degree at least k−1 within L since it can lose only w. Every port has degree at least k−4 in L since it can lose only w and A. Take e=0 to require a spanning path beginning at an arbitrary prescribed vertex, or e=1 to require Hamilton-connectedness. Each conclusion holds if either

    m+e ≤ 2(k−4),

or both

    m+e ≤ 2(k−1)   and   p ≤ k−5−e.

For e=0 adjoin a leaf at the prescribed start and apply Hamilton-path closure at threshold m. For e=1 adjoin a degree-two marker at the two prescribed distinct endpoints and apply Hamilton-cycle closure at threshold m+1. Ordinary cycle closure gives the path version by adjoining a universal vertex. In the first numerical range all original vertices complete immediately. In the second, all remotes complete to a clique of order m−p. Each remote has degree at least m−p−1, so its degree sum with any port is at least m−p−1+k−4≥m+e, completing all cross edges. At that point each port has degree at least max(k−4,m−p). If the first numerical range does not apply, m+e≥2k−7; since p≤k−5−e, one has 2(m−p)≥m+e. This completes the ports too. The original clique and the designated marker have the desired spanning path or cycle, which reverses under closure. Removing the marker supplies the prescribed original endpoint or endpoints.

**A part opposite an intrinsically deep remote.** Suppose E contains some x∈R with d_C(w,x)≥3. Then the distance count in `degree-three-complement-cut.md` gives |R∩D|≤k−2. Consequently

    |D| ≤ |T∩D|+k−2 ≤ 2k−3.

The last inequality uses that E contains a port. More precisely, with d=k−|T|, p_E=|T∩E| and j=1 if w∈T and 0 otherwise, the bound is |D|≤2k−2−d−p_E−j. If |T∩D|≤k−6, D is Hamilton-connected by the closure criterion; if |T∩D|≤k−5, a spanning path from every prescribed vertex follows. These conclusions hold at arbitrary order and with no restriction on which anchors the ports see. In particular k≥7, Hamilton-connectedness of E, and |T∩D|≤k−6 imply traceability of G. With an anchor edge, |T∩D|≤k−5 suffices.

If the displayed criteria do not supply the two-ended path through D, then p_D=|T∩D|≥k−5 and |D|≥2k−8, hence |R∩D|≥k−7 since p_D≤k−1. All ports in E, all port membership of w, and the deficit d have combined total ≤5. If a one-ended path in D is all that is needed, failure of its sufficient criteria forces p_D≥k−4, |D|≥2k−7, and |R∩D|≥k−6; the same remaining port-plus-deficit total is at most four.

This proves the specified rooted path and gluing cases. An arbitrarily large opposite component is not automatically Hamilton-connected. The possibility that both parts have all remotes at C-distance at most two from w also remains.

## A single anchor cannot cover the deep side's ports at higher orders

In the deep-opposite case put P=T∩(E∪{w}), j=1 if w∈T and zero otherwise, d=k−|T|, and s=n−(3k+2)>0. Fix any anchor a. Let f count its positive even-distance witnesses outside R∩E. Let h count vertices of E in the third layer of z whose distance from a is odd. Any remote in E is in the third, fourth or fifth layer of z. The fourth layer contains at most d vertices by the even budget at z; the fifth layer is at distance exactly four from every anchor by the high-pair distance bound. All E remotes except at most d+h are therefore positive even-distance witnesses of a. Thus

    |R∩E| ≤ k−f+d+h,
    h ≥ s−1+j+(k−2−|R∩D|)+f.

The second inequality follows from the partition n=4+(k−d)+|R∩E|+|R∩D|+1−j. If D has a remote, f≥1. Indeed if a misses another anchor it sees it at distance two through z. Otherwise a sees the other anchors; any missed D port then has distance two through another anchor. If no D port is missed, the connected D contains an edge from some port to a remote, giving an even-distance witness in D. If D has no remote, k−2−|R∩D|=k−2≥1 instead. In either case h≥s+j≥1. Every third-layer remote in E has a neighbor in P: any port in C neighboring it lies in E or equals w. If a covered P then all such remotes would have distance two from a, contradicting h≥1. Thus each of the three anchors misses at least one P vertex. This exclusion works even when z has eccentricity five.
