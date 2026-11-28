# Independent handoff and independent computation for four ports at k=6,7

I checked split/k6-four-port-census.cpp SHA-256 5d285b91b42311fbbcf775acf206db97e8464077dea4e560f1ecc55c7ddd7714, the corresponding manuscript and its parameterized source. Independently written sources review/k6-four-independent.cpp and review/k7-four-independent.cpp and captured .log files reproduce the exclusion of every high-order graph in both cases.

The only input about traceability in this exclusion is that the previously settled order range ends at n≤3k+2. With (4,4) above that range the core R lies entirely in the third layer, every member has a port contact, h≥2k−3, and D=P∪R is connected. The pure component K is forced to be a (k−4)-clique complete to all five anchors, since each member has exactly k potential neighbors. The shell enumeration uses no appeal to a hoped-for Hamilton route in D.

Each port must have an anchor and no anchor may meet all four ports (h>k). Sorting the five anchor sets and quotienting by all four-port permutations preserves all possibilities as all 1024 labeled graphs on those anchors and all 64 labeled port graphs are then tested. The 546 surviving incidence representatives are orbits of the bipartite incidence relation alone, not 546 completed graphs. Equal masks and equal (mask,port-distance-two-set) pairs within equal mask groups can be sorted on the remote side because any remote graph edges have yet to be prescribed. The maximal permissible remote graph respects these relabelings.

I built the skeleton as an ordinary vertex adjacency matrix encoded by row bitsets: z, five anchors, all forced K vertices and four distinct ports. The known second neighbors of any shell vertex are calculated by taking the union of the neighborhoods of its neighbors then deleting its closed neighborhood. The additional K vertex for k=7 is allocated at index 30 outside the port/core index range; it is adjacent to both other K vertices and all anchors. The second-neighbor count is valid before unknown remote edges are present: adding remote–remote edges cannot destroy an already exhibited length-two path from a shell vertex to another nonadjacent vertex. After fixing the port–remote masks the same applies to known shell–remote distances two, since no new port–remote edges are subsequently allowed.

For every anchor its remote support union costs at least its cardinality in independent distance-two slots. The additional uniform bound k−1 follows from the proved extra witness; port supports have the same bound. For each p write s_p for its degree upper bound in the core and b_p for its still available remote-even slots. A remote singleton on p needs an exterior neighbor, so can exist only if s_p+b_p≥k, and must itself be a distance-two witness at some other port. Therefore the two private-count bounds and the general union-size inequality used to upper-bound h are valid. Every port-incidence union cap may be passed to subsets and combined additively on disjoint subfamilies. These constraints only enlarge the candidate set.

The independent program explores multiplicities of the 15 possible nonempty port masks. For each resulting incidence graph it recomputes graph-theoretic second neighborhoods from the explicit adjacency matrix and extends the known remote-even contacts with optional subsets of nonneighbor ports. Every private vertex must have at least one such witness. If xy is a remote edge, each of x's incident ports missing y must be an allowed distance-two port of y, and conversely. Construct all allowed edges, then check every remote ambient degree and run an ordinary graph search for connectivity on the induced graph on ports and remotes. The allowed graph is a supergraph of the true D, so loss of the degree or connectivity test is at all times a sound rejection. Additional positive-even constraints were not needed.

Results: each k has 546 initial incidence orbits. For k=6 the maximum shell order bound is h=10; h=9 has 36 incidence assignments, 266 boundary extensions and no degree survivor, and h=10 has 4,4,4,0 connected. For k=7 the maximum is h=12; h=11 likewise has 36,266,0, and h=12 has 4,4,4,0 connected. The degrees in the final allowed remote classes force cliques of sizes k−1, with disjoint pairs of ports and no possible intercomponent edge. In particular no multiplicity reduction has suppressed a connected realization, and these counts do not count isomorphism classes of full graphs.

Combining the analytic k≥8 four-port theorems with the two computations proves that no unresolved (4,4) parameter remains. Together with all the independently checked other parameter pairs and the exceptional three-component k=6 branch, every disconnected G−N[z] case with a degree-five unique low vertex is traceable under the prior lower-order/remote-component results. The unrestricted conjecture and the case where G−N[z] is connected are separate.

## Reproducibility

Source SHA-256 hashes at this audit:

    split/k6-four-port-census.cpp        5d285b91b42311fbbcf775acf206db97e8464077dea4e560f1ecc55c7ddd7714
    split/four-port-param-explore.cpp    e5e077ee2751e988169d52da0c426386114f12e234148ff6219bc025af76061f
    review/k6-four-independent.cpp       a71c36bacc9163089fc95175d71af34cefab76992418c14535062c07c7650691
    review/k7-four-independent.cpp       d7f49f0ba7741267c02ab8dc9af89869d5edf835bf830c79b47a61fc8bcc5692
    split/degree-five-k6-four-port-census.md 2055a91a3e97392c7c619853cb6b58302480dd30fa9ccd6676ea8ce10cf3e5b2

From the run root, in an active authorized session, replay these standard C++17 programs with:

    g++ -O3 -std=c++17 review/k6-four-independent.cpp -o /tmp/g189-review-k6
    /tmp/g189-review-k6
    g++ -O3 -std=c++17 review/k7-four-independent.cpp -o /tmp/g189-review-k7
    /tmp/g189-review-k7
    g++ -O3 -std=c++17 split/four-port-param-explore.cpp -o /tmp/g189-original-parameterized
    /tmp/g189-original-parameterized 6
    /tmp/g189-original-parameterized 7

The independently captured stdout is stored in review/k6-four-independent.log and review/k7-four-independent.log. Recompilation requires no solver, random seed, network or external library.
