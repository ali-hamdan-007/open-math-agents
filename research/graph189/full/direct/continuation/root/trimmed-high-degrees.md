# Deleting several exceptional high-degree vertices

Write k for the second-smallest degree of a qualifying graph, h=ceil(k/2), and n for its order. Assume k≥3. Let T be any set of at most h+1 vertices for which H=G−T is connected and nonempty, and choose z of minimum original degree among vertices of H. For an induced path u,w,v of H with endpoints different from z, put

    b = |T∩N(u)∩N(v)| − |T∩(N(w)∖(N(u)∪N(v)))|,
    E = d(w)+e(w)−d(u)−d(v),

where all neighborhoods, degrees and positive even-distance counts on the right are taken in G. The following order condition suffices for a spanning path in G:

    n > 3k+1+(k−2)E+(k−1)b for every such induced path.

Indeed let j_G and j_H be the local Ore defects of the same wedge in G and H. For every deletion, removing a common endpoint neighbor increases j by one, removing a center neighbor absent from both endpoint neighborhoods reduces it by one, and any other deletion preserves j. Thus j_H=j_G+b exactly. By the refined penultimate inequality in `../verify/wedge-order-refinement.md`,

    (k−1)j_H ≤ 3k+2−n+(k−2)(1+E)+(k−1)b.

The strict hypothesis makes the right side < k−1. Hence j_H≤0 for all rooted wedges. The kernel-checked local Ore theorem `Graph189RootedTrace.rooted_local_ore` supplies a Hamiltonian path rooted at z in H. In G this path omits at most h+1 vertices; `../lowblock/all-near-spanning.md` and its exterior-size bound supply a Hamiltonian path in G. Only the local Ore theorem has a Lean certificate here. The full deletion consequence is a written argument.

In particular, take T to contain all vertices of degree above k. Except at z, vertices of H have original degree k, hence E≤0. If every nonadjacent pair of H other than z which shares a neighbor in H has at most one common neighbor in T, then n≥4k+1 suffices (in fact n>4k). At smaller orders the previously audited moderate-order theorem covers κ≥3. Consequently every qualifying graph of connectivity at least three with at most two vertices above k is traceable unless those two vertices have a pair of nonadjacent common neighbors sharing a third common neighbor outside the two vertices. In this obstruction the pair of common neighbors can be required to omit the selected root. The two deleted vertices cannot disconnect a graph of connectivity three, and the size limit on T is automatic. This conclusion holds for any k≥3. The same theorem holds for more hubs whenever their deletion satisfies the two stated conditions. More generally n>3k+1+(k−1)t suffices if t is the maximum common hub count among such pairs, independent of the actual degrees of all hubs.
