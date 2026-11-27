# Erdős 307 and its coprime variants

Barbeau's original question asks whether there are finite sets of primes P and Q for which the product of their reciprocal sums is exactly 1. This prime-only question remains open in the sources reviewed. It has a known lower bound of 60 primes across the two sets.

When the entries of each side need only be pairwise coprime, allowing the unit gives elementary examples. Cambie's sets {1, 5} and {2, 3} give reciprocal sums 6/5 and 5/6. The 1-free Formal Conjectures statement requires finite sets of natural numbers, each with at least two members, pairwise coprimality on each side, no 1 in the union, and no 0 in the intersection. The size condition, pairwise coprimality, and exclusion of 1 also rule out 0 on either side.

Doug Phillips announced a 1-free witness on November 26, 2026. The certificate uses 914 deviations, 913 additions to its left base, and two closing terms, producing 968 elements on the left and 5 on the right. Computing the first three added terms exactly from the published recurrence gives 1523, 1657, and 5,134,177. The third is composite, equal to 409 × 12,553. Palomar checked the exact 1-free statement against Formal Conjectures and reported the standard Lean axioms only. Its pinned Solution.lean contains the proof.

- [Bonfioli’s 60-prime bound](https://github.com/ElVec1o/erdos307/blob/36c3b7979a77e003fcf47016e41f2f7133495415/lean/Erdos307/Sixty.lean)
- [Original problem and elementary coprime examples](https://www.erdosproblems.com/307)
- [Phillips's certificate and verifier](https://github.com/duggiephresh/unit-fraction-solutions/tree/main/erdos307-coprime)
- [Phillips's description of the recurrence](https://github.com/duggiephresh/unit-fraction-solutions/blob/main/docs/METHOD.md)
- [Pinned Lean proof](https://github.com/duggiephresh/palomar-unit-fractions/blob/e63a19d0145943e30f8d942b9396c2f9d729f0e5/Solution.lean)
- [Palomar registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000045&version=1)

The OMA and Formal Conjectures integration changes seen in the read-only audit were still open. OMA #1601 updates status metadata. OMA #3898 ports Phillips's public proof and certificate. OMA #4257 credits Phillips and uses a separate 791-deviation chain and checker for the same statement. Formal Conjectures #8318 changes only the variant's status and proof reference, preserving its statement. These are all scoped to the 1-free coprime variant.

- [OMA metadata #1601](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1601)
- [OMA Phillips proof port #3898](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3898)
- [OMA independently generated proof #4257](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4257)
- [Formal Conjectures integration #8318](https://github.com/google-deepmind/formal-conjectures/pull/8318)
