# Verification of the isolated A056777 reduction

- The exact submission passes the repository lint gate.
- Pinned Lean 4.33.1 elaborates the submission against focused parent artifacts. The axiom audit reports only propext, Classical.choice, and Quot.sound.
- The submission also elaborates with actual Mathlib Graph.Subgraph and Matroid.Minor.Order prepended. These modules define the notation involved in the earlier collisions. Three missing dependencies were compiled in an isolated overlay. The historical synthetic notation probes independently pass.
- An isolated checkout at the project's pinned Formal Conjectures commit was staged for the unchanged tools/check.sh. A Lake no-build preflight returned an infrastructure fault while preparing the parent import. FormalConjecturesUtil imports the Mathlib umbrella, and the pinned local cache lacks Mathlib.olean and 2,934 of the 8,313 umbrella modules. The full-import check therefore did not reach the submission. No large rebuild or shared Formal Conjectures changes were made.

The checked submission has SHA-256 9f07dfb54749ad077ca59a50642e12483a0f2ca2d9652fb4ad5f112f03c42942.

## Full-import recovery attempt

The pinned Mathlib cache is reachable via its official master endpoint with IPv4. Curl HTTP/2 multiplexing and leantar extracted the 2,933 missing outputs into a private /dev/shm overlay in two passes, using 2,108,571,648 bytes. The isolated checker reused the exact-revision local package caches. A second Lake preflight still reported a small set of stale traces, so the canonical checker was launched with actual rebuilding enabled and constrained to two CPU cores. It used the staged repo only. No shared artifacts were deleted or overwritten.

The final monitored four-thread invocation remained inside Lake without writing a Formal Conjectures olean or reaching the submission for more than three minutes. It was stopped to avoid continued resource use. The recovered cache is available in the isolated workspace, and no canonical verdict was produced. A parallel raw Mathlib import smoke test was killed under memory pressure and also produced no verification result.

## Direct full-import attempt

The 285-source dependency order and SHA-256 manifest are in the direct workspace. Lean 4.33.1 identifies itself as 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Formal Conjectures and Mathlib are at 9097e2f90e66d2f6244209cb1c07f7120d17ec53 and 0df444a360eaa60ab8c11dca51a86af692955474 respectively. The three staged ancestor files match upstream GitHub main blobs 693f6c33e0b357d123365757e06df93ccd71fbb4, f44b5ff0c4d692543066955a5dc3285bc31b94da, and b797d9cb1bf07b2ce1ae8c5bfdc242905c05567f byte for byte. The direct scheduler runs one Lean process at a time and only appends the standard axiom audit to the unchanged final source.

The direct run reached its 240-second per-module limit on its first, dependency-light linter. That source imports only Lean and Init modules. At timeout the process was still sleeping, with no diagnostics and no olean. During the run the host showed 33–53% I/O wait. The final submission was never reached, so the earlier focused and notation-probe results remain the verified results.
