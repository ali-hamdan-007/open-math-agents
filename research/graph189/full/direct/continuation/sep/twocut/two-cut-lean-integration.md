# Separating-pair formalization handoff

The unrestricted separating-pair statement is already covered by independently reviewed paper proofs on the fork. The degree-nine and degree-ten notes in this directory are independent elementary routes designed for direct Lean verification. Both passed independent paper audit. They do not add a solved graph range or an official verdict.

## Pinned checks completed earlier in the session

- Graph189TwoCutSelectJoint.exists_connected_least_cut selects the globally smallest side of a genuine 2-cut and gives two connected sides.
- Graph189TwoCutCensusJoint checks the common-free arithmetic, both-private arithmetic and ambient complementary-parity rows.
- Graph189TwoCutRecut, Graph189TwoCutLayout and Graph189TwoCutShallow compile with fresh-import axiom audits. The shallow wrapper establishes the actual graph bound n ≤ 3k+2 when the selected shallow side touches p at exactly k−1 vertices and the opposite side exceeds 2k+1.
- Graph189TightTwoCut.index_three checks the original-graph order lower bound n ≥ 4k−5 at k ≥ 7. It is in Graph189AllIndexThree.
- The imported dense-route inputs Graph189RootedTrace.rooted_local_ore and Graph189TerminalLeafClosure.prescribed_of_supergraph are already checked.

## Smallest next verification

1. Check Graph189TwoCutOnePrivateEarly by itself. It only imports the checked census joint and handles the full-anchor and smallest-side alternatives. The original unsplit file ran out of memory without a diagnostic and is superseded by this split.
2. Check Graph189TwoCutOnePrivateFinal once Early has an olean. It reuses the checked actual shallow wrapper.
3. Check Graph189TwoCutResidual. It imports the checked selector, index-three and edge order, and discharges the missing-private case. It preserves the least-side certificate for later recuts.
4. Verify Graph189TwoCutJoin separately. It adds the chosen separator vertex to two original-edge side paths and transfers the exact omission count.
5. Graph189TwoCutTraceability.near_of_routes combines those interfaces. The three case routes remain explicit. Its companion traceable_of_gap leaves the complete original-graph path gap as a separate obligation.

Use one leased warm job and Werror at a time. The smoke check uses a fresh consumer and verifies the printed axioms. Existing unrelated compiler locks take priority under the coordinator.

## Source-only route dependencies

- Graph189RootedRotation gives a support-preserving rotation with fixed far endpoint and an injective family of candidate starts.
- Graph189LongestDegreeSum bounds a longest path through endpoint degrees, and Graph189RootedLongPath adds one exceptional vertex and a bounded forbidden set.
- Graph189TwoCutCommonFreeRoute transfers the rotation bound to a genuine side with original degree counts. The common-contact branch still needs a separate wrapper for deleting a possible internal low leaf.
- Graph189TwoCutDenseRoute gives actual prescribed starts at the Dirac floor using the checked rooted local Ore theorem, with no separate cycle theorem.
- Graph189TwoCutShallowArithmetic keeps the degree-nine one-unit slack, degree-ten row equalities and both small gate widths as exact natural arithmetic.
- Graph189TwoCutSaturatedGate obtains the finite two-arm layout from a saturated nonuniversal private port. Its two minimum recuts give the lower order on both arms.
- Graph189TwoCutArmOre obtains prescribed-endpoint Hamilton paths in high induced arms using the checked PrescribedBatch result. The low-contact gate joining and universal-port alternatives are still paper.
- Graph189TwoCutCensus, Graph189FarPrivatePort and Graph189AdjacentAnchorOrder contain the remaining source-only metric and census inputs. The balanced cases and the full longest-path gap still need formal assembly.

The selected proof dependencies do not imply a complete checked connectivity-two proof yet. No submitted or upstream accepted result is claimed here.
