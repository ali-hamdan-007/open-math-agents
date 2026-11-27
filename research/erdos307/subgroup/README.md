# A subgroup restriction for Erdős problem 307

Let `S = P ∪ Q` be the prime support of a putative solution, and write
`N = ∏S` and `C = ∑_{p∈S} N/p`. The reduced reciprocal sums give
`AB = N` and `A² + B² = C`, where `A = ∏P` and `B = ∏Q`.

At an omitted odd prime ℓ, let `H` be the subgroup of `Fℓˣ` generated
by the residues of the support primes. Define `K = H²` and `m = |K|`.
Use the Dickson trace with `D₀ = 2`, `D₁ = C`, and
`Dⱼ₊₂ = C Dⱼ₊₁ − N² Dⱼ`. Its power-sum identity gives
`Dⱼ = (A²)ʲ + (B²)ʲ`. Because `A², B² ∈ K`, a solution forces
`Dₘ = 2` in `Fℓ`. One can compute `m` as the least common multiple
of the orders of the individual squared support residues.

This condition is exact for the local equations with factors in `H`.
Take the roots `x,y`, counted with multiplicity, of
`T² − CT + N²` in an algebraic closure of `Fℓ`. Then
`xᵐyᵐ = (N²)ᵐ = 1` since `N² ∈ K`. If `Dₘ = 2`, the two
values `xᵐ,yᵐ` have sum 2 and product 1, so both equal 1.
The `m` elements of `K` exhaust the roots of `Tᵐ − 1`.
Choose `a ∈ H` with `a² = x` and put `b = N/a ∈ H`.
Then `ab = N` and `a² + b² = C`. This converse is a paper proof.

The ambient version `m = (ℓ−1)/2` is equivalent to the existing
paired-square sieve of Bonfioli, which tests `C+2N` and `C−2N`.
The subgroup condition is strictly stronger on some supports. For
`S = {11, 41, 101}` and `ℓ = 5`, the ambient square residues are
0 and 1, and the internal cofactor-square tests also pass. All three
support primes are 1 modulo 5, so `K = {1}` and the subgroup screen
requires `C ≡ 2`. In fact `N = 45551` and `C = 5703 ≡ 3`.
The example has reciprocal mass below 2 and tests the logical strength
of the congruence.

At the smallest omitted prime, all primes below ℓ belong to the
support. Each integer 1 through ℓ−1 factors into those primes, so
`H = Fℓˣ` there. The restriction can add information at later
omitted primes. It gives a local obstruction and establishes no
new cardinality bound.

## Arbitrarily large reciprocal mass

The strictness persists for supports of arbitrarily large reciprocal
mass, even while passing the ambient paired-square screens at any
prescribed finite set of odd omitted primes. Include 5 in that set.
Let `M` be 512 times the product of the prescribed primes and choose
a size `k` satisfying `k ≡ 66 (mod 512)`, `k ≡ −2 (mod 5)), and
`k ≡ 2 (mod ℓ)` at every other prescribed prime. Choose the first
`k−1` primes congruent to 1 modulo `M`. The sum of their reciprocals
grows arbitrarily large along the allowed sizes because the reciprocal
primes in that progression have a divergent sum.

Write `N₀` for their product. Choose one further prime `r ≡ 1 (mod M)`
satisfying `(r/p) = ((N₀/p)/p)` for every chosen prime `p`, where
the outer parentheses denote Legendre symbols and `N₀/p` is a quotient.
For each `p` either symbol can be prescribed by a nonzero residue class.
The Chinese remainder theorem and Dirichlet's theorem give such an
`r` distinct from the preceding primes. For each preceding prime the new internal
cofactor symbol is then the product of two equal signs and hence 1. All the primes are 1 modulo 4, so
quadratic reciprocity gives
`(N₀/r) = ∏ₚ (r/p) = ∏_{p<q} (q/p)(p/q) = 1`.
Thus the final support passes every internal cofactor-square test.

At the prescribed odd primes `N ≡ 1` and `C ≡ k`. The ambient
square residues are therefore 0 and 4 at each prescribed prime
other than 5, and 0 and 1 at 5. Moreover `C−2N ≡ 64 (mod 512)`
and `C+2N ≡ 68 (mod 512)`, so both are 2-adic squares. Their
2-adic valuations are 6 and 2, with respective odd unit parts
congruent to 1 modulo 8. At 5 the subgroup is trivial and
`C ≡ −2` fails the subgroup congruence. This construction is a
paper proof.

## Lean replay

The two necessity theorems and the strict example are checked in Lean
4.33.1 with mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. In a Lake workspace with
that toolchain and dependency, copy the three Lean files into the working
directory and run the following sequence.

```sh
lake env sh -c '
  export LEAN_PATH=".${LEAN_PATH:+:$LEAN_PATH}"
  lean -o Erdos307CrossCoprime.olean Erdos307CrossCoprime.lean &&
  lean -o Erdos307OmittedPrime.olean Erdos307OmittedPrime.lean &&
  lean Erdos307Subgroup.lean
'
```

The final file reports `propext`, `Classical.choice` and `Quot.sound`
for the necessity and finite checks.
