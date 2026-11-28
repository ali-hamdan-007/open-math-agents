# Two all-order theorems for the original Graph 189 hypotheses

Let k be the graph’s second-smallest degree counted with multiplicity and κ its vertex connectivity. A finite connected simple graph satisfying the original even-distance bound has a Hamiltonian path whenever either of the following holds.

* k ≥ 26 and κ ≥ 5, proved in Graph189LargeDegree.traceable.
* k ≥ 19 and 3κ ≥ k, proved in Graph189ThirdConnectivity.traceable.

Both conclusions are unconditional on graph order. The high-degree theorem splits at 3κ = k. Below the split, native linked sets in the universal completion give either a Hamiltonian path or a minimum-degree vertex whose deletion is traceable. In the latter case a rooted longest-path matching and two tight gaps force too many original distance-two witnesses. At and above the split, both minimum-deletion alternatives give the same lower order with parameter ceil(k/3), contradicting the graph’s maximum-degree width inequality.

The remaining high-degree two-connected case has κ equal to 2, 3 or 4. Smaller degrees also require work. The exact parent still awaits a full formal proof.

## Reproduction and credit

The saved archive contains 129 Lean sources, a topological manifest, a regeneration script for the 130th source, and the audit logs. Its SHA-256 is 3f9ac57744e3aa67c2f55b82202c9e1136b0d2a5fa27107edf670b5e58b6b605. Run replay-large-degree.py as described in its README. Source digests were validated on the extracted archive. Final integration elaborated locally with Lean 4.33.1 and a separate import printed propext, Classical.choice and Quot.sound for all three named theorems. A full clean rebuild from the distributed archive is separate from these checks. The Graph 189 results have no official verdict.

The linked-set argument reuses @koolkao's accepted OMA PR 7971 on the Ma–Ning–Zhao Bondy theorem. Credits for this fork integration include Ali Hamdan, Codex, gpt-6.2-sol and gpt-6.2-astra. Upstream repository ID 1471973920 now resolves under lefttosolve2/open-math-agents.

[Upstream linked-set proof](https://github.com/lefttosolve2/open-math-agents/pull/7971) · [Proof archive](large-degree-proof.tar.gz) · [Independent import](../verify/parent-residual/range-import.log)
