# A degree-sum bound on the number omitted from an arbitrarily large side

Let B be a connected component at a minimum separator as in the contact-path note. Write b=|B|, let N count its nonports, and let δ, α be its **internal** minimum degree and independence number. For α≥3 let σ be the smallest sum of the three internal degrees in an independent triple of B. If σ≥b, B has a path omitting at most

    Q=max(0, α−1−ceil(σ/3))

vertices. If α≤2, B has a spanning path (the argument below uses Chvátal–Erdős, or an elementary endpoint-splicing argument).

Adjoin a universal vertex x to B. The result H is 2-connected for b≥2 since B is connected. Its independent triples are the triples in B, with degrees increased by one, and its independence number is α. Thus σ₃(H)=σ+3≥|H|+2. The long-cycle theorem of Bauer and coauthors gives c(H)≥min(|H|,|H|+σ₃(H)/3−α), whence the displayed bound on the number missing from a longest cycle. If the cycle contains x, delete x to get the B path; if it avoids x, open it inside B at any vertex. When α≤2, κ(H)≥2≥α(H) makes H Hamiltonian by Chvátal–Erdős. The b=1 case is immediate. The graph here is connected B with one artificial universal vertex; the vertex needs no genuine contact because the endpoint trimming below is carried out in the actual graph.

For a finite upper bound that avoids computing α, let E be the minimum number of vertices **outside B** at positive even distance from a B vertex in G. Then

    α ≤ max(k−E+1, b−2δ).

Indeed, if some pair of members of an independent set I has no common neighbor in B, the disjoint B-neighborhoods of the two members are disjoint from I and use at least 2δ vertices. Otherwise each vertex of I sees every other member at distance two, using |I|−1 slots in addition to its ≥E outside slots. This estimate uses the original even-distance condition on G, not an assumed cap in its induced side.

If b−Q>N the certified B path contains a genuine port. The terminal nonport runs are disjoint and together use at most N vertices; trimming the shorter to the first port loses at most floor(N/2) additional vertices. Thus the total large-side omissions are at most

    Q+floor(N/2).

At s=3 and with a high nonport across the cut, N≤k−3+1_{low nonport in B}, uniformly in b. Subtract the actual number of omitted nonports from N when known. Any savings in how many anchors the small side absorbs go directly into the allowance for Q (see absorbing-the-separator.md). This computable sufficient bound can apply when b grows beyond 3(k−s), since σ uses the actual internal degrees of independent triples. If σ<b this particular long-cycle estimate supplies no new conclusion. It is not a universal large-side bound for Graph 189.

Source: D. Bauer, G. Fan and H. J. Veldman, Hamiltonian properties of graphs with large neighborhood unions, Discrete Mathematics 96 (1991), Theorem 11 (citing their reference 2), https://ris.utwente.nl/ws/files/7044448/Bauer91hamiltonian.pdf.
