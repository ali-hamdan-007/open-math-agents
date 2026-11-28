# Formal components of the exterior argument

Graph189GatewayRank.lean proves the cardinality estimate used for the additional core vertices in the finite certificate. For any finite sets of rows W and candidates Z in a simple graph, if every member of W misses at most a vertices of Z, at least i+1 candidates have at least |W|−⌊|W|a/(|Z|−i)⌋ neighbors in W whenever i<|Z|. The proof counts missing incidences in the two orders. Graph189GatewaySelection.lean extracts a list of g distinct candidates meeting the g successive estimates.

Graph189TerminalLeafClosure.lean defines the augmented graph on V ⊕ Bool. The two added vertices have degree one, with original neighbors u and v. The spanning-path edge-closure theorem from Graph189TraceClosurePublic applies there to any missing old edge whose original degree sum is at least |V|+1. Graph189LeafEndpoints.lean proves that both leaves are endpoints of any spanning path. Its proof compares the predecessor and successor of an interior leaf and uses injectivity of the path's vertex sequence.

Graph189LeafStrip.lean extracts the original u–v Hamilton path. Graph189PrescribedClosure.lean applies this extraction to the prescribed-endpoint edge-closure theorem. Graph189PrescribedBatch.lean iterates this operation over a finite set of missing edges and constructs a Hamilton path of the complete graph with any two distinct endpoints. Graph189ExteriorClosure.lean applies those results to the two sufficient conditions on a proposed larger core K, one allowing one low-degree vertex, and one using a specified dense set W.

Graph189ExteriorGap.lean proves that replacing an interval on a longest path with a disjoint path forces the interval to contain at least as many vertices as the replacement. Empty initial or final intervals are included.

The compiled .olean and log for each module record its verification state. Source files and filter inputs for the separate integer calculation are in the parent directory. The graph-to-exterior decomposition and the full Graph 189 statement require further formalization.

## Portable replay

From a built mathlib project at the revision in upstream/mathlib-revision.txt, set MATHLIB_PROJECT to its absolute directory and run ./portable-replay.sh. The script copies the ten source files to portable-build and runs Lean with warnings as errors. The pinned Lean toolchain is listed in upstream/lean-toolchain. The original edge-closure proof is included under upstream, so the portable run recompiles the non-mathlib dependency from source. The local replay output in clean-replay.log records the nine downstream module checks and all exported axiom lists.
