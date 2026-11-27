# Lifting a quadratic witness modulo 43

Let S be a finite set of distinct odd primes omitting 43, with sum of reciprocals at least 2. Start from any subset of S and fix the placement of up to six primes. While preserving those placements, the subset's cardinality parity and its squared product modulo 43, one can realize **every** reciprocal sum modulo 43. In particular, an admissible quadratic witness for the two swap equations lifts to a simultaneous modular witness. Reserving three primes on each side preserves the required minimum side sizes. The other side sizes may vary.

## Two progressions from each opposite pair

Write ℓ for the modulus, an odd prime. After removing reserved primes, let m and n be the populations in residue classes r and −r, and let d be the least common multiple of 2 and the multiplicative order of r². It suffices to preserve the combined selected count modulo d in each pair.

For a single population m whose selected count starts at a, varying the count by multiples of d gives width floor(a/d)+floor((m−a)/d), at least s(m)=max(0,floor((m+1)/d)−1). The two residue classes have opposite reciprocal increments, so these progressions combine into a progression of width at least s(m)+s(n), with nonzero step d/r. Width counts the number of steps.

Alternatively, let M=m+n and choose a permitted combined count t closest to M/2. If M≥d, its distance from M/2 is at most d/2, and it belongs to [0,M]. The number selected from class r then ranges from max(0,t−n) to min(m,t). Its width is min(m,n,t,M−t). This guarantees a progression of step 2/r and width at least max(0,min(m,n,floor((M−d+1)/2))). For M<d the claimed lower bound is zero and the original split suffices.

Choose the wider construction independently for each opposite pair. If the sum of widths reaches ℓ−1, every sum occurs. Indeed adding a two-point set with a nonzero difference to a proper nonempty subset of the prime field increases its size, since translation by that difference generates the additive group. Fixed contributions translate the result.

## Integer certificate

If saturation fails, allocate at most ℓ−2 width units among all pairs. A pair allocated q units must satisfy s(m)+s(n)≤q. Also, if m,n>q it satisfies M≤2q+d. These inequalities bound both populations. For each permitted population and allocation of reserved primes, the largest possible mass comes from the first eligible primes in each class. The script uses upper-rounded integer reciprocals and maximizes these upper bounds over all allocations by dynamic programming. The independently coded audit uses a looser population envelope.

At ℓ=43 the mass bounds with zero and six reserved primes are respectively 1.901542459432 and 1.905724184659. The independent calculation gives 1.9068040768 with six reservations. All are strictly below 2. This resolves the local lifting question left by opposite43.md for arbitrary qualifying supports at this modulus. It is a paper proof with executable integer certificates.

Research workers and independent verifier: gpt-6.2-sol.

## Other moduli

The paired bound with six reservations also works at primes 47, 53, 61 and 73. The independent six-reservation upper bounds at those primes are 1.9631272780, 1.9187985047, 1.9218438094 and 1.9478841278. Combined with the earlier bounds this covers every odd prime through 53. The bound computed at 59 exceeds 2.

For an odd composite M assume S is coprime to M and start from one witness modulo M. If each unit class r has d_r=lcm(2,ord_M(r²)) relatively prime to M, the single-class increments d_r/r each generate the whole additive group. The elementary argument in parity-saturation.md therefore works verbatim with M−1 steps. The support-size threshold with six reservations is 7+max(d_r)(M−2)+2Σ(d_r−1), summed over units. If the first threshold-minus-one eligible odd primes have reciprocal mass less than 2, the desired simultaneous lift follows. composite_mass.py certifies this at 17 odd squarefree composite moduli up to 150, including 145=5×29. Here a single partition works at both prime factors. Existence of a common starting quadratic witness remains a hypothesis.
