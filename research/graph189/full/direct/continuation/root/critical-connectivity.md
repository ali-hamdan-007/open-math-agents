# A free vertex in a finite graph

For a finite simple graph with connectivity κ, minimum degree δ and order n, suppose κ<n−1 and 3κ<2(δ+1). There is a vertex z outside every separating deletion of size κ. Making z adjacent to every other vertex raises vertex connectivity to at least κ+1. Both statements are theorems in Graph189CriticalConnectivity.lean. They formalize the classical critical-connectivity bound used in the Graph 189 order argument.

## Proof

Call one side of a minimum separation a fragment and take a fragment A of least possible order. Let S be its separating set and B the opposite side. If a second minimum separator T meets A, write C,D for its two sides. The boundary of A∩C is contained in the disjoint union of A∩T, S∩T and S∩C. If A∩C is nonempty, then it is strictly smaller than A, so the size of this union exceeds κ. The opposite corner B∩D has complementary boundary size below κ because the two corner boundary counts add to 2κ. Thus B∩D is empty. Also |S∩D|<|A∩T|, by comparing the first boundary count to |S|. It follows that |D|=|A∩D|+|S∩D|<|A|, contrary to minimality. Interchanging C and D proves A⊆T.

For the bound on its size, consider C. If B∩C is empty then C⊆S, so |S∩C|=|C|≥|A|. Otherwise apply the minimum cut bound to the boundary of B∩C and compare it to the partition of T into A∩T, S∩T and B∩T. This again gives |S∩C|≥|A|. The same holds on D, hence 2|A|≤κ. Every vertex of A has degree at most |A|+κ−1. The assumed lower bound on δ now precludes any minimum separator meeting A. Any vertex of A can serve as z. If no minimum separating deletion exists, choose any vertex.

After completing z, every deletion retaining z leaves a connected graph. A separating deletion through z of size at most κ was already impossible in the original graph, either through the chosen free vertex or by minimality of κ. The resulting graph has connectivity at least κ+1.

## Reproduction and use

In a pinned formal-conjectures checkout with mathlib and the two imported graph definition modules built, run the following from this directory.

```sh
python3 replay-modules.py --project "$OMA_FC" Graph189CriticalConnectivity
```

Graph189CutCorner constructs an actual graph separation, Graph189AtomCounts checks the corner count, Graph189Atom proves the fragment assertion, and Graph189Removable chooses the vertex. Graph189CriticalConnectivity applies this to the registered graph invariants. The local pinned kernel reported only propext, Classical.choice and Quot.sound. The remaining long-cycle order theorem is a separate mathematical input.
