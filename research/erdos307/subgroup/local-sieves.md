# Local partition checks for prime-only Erdős 307

For a prime support S, write N for its product and C for the sum
of its cofactors. At a modulus coprime to N, a partition has
products A,B and reciprocal sums U,V with AB=N and U+V=C/N.
The exact ordered swap tests are AU=B and BV=A. They imply
the square test A²+B²=C and the reciprocal-product test UV=1.
Tracking (product, reciprocal sum, cardinality) for subsets
preserves all the information these local equations use. This is
ordinary finite reachability, with a state update by multiplying
by p and adding 1/p when p is selected.

Bonfioli's `Pythagorean.lean` and `PairLocal.lean` develop the
paired-square tests. His `SplitSieve.lean` and `SplitExact.lean`
already track genuine partitions in single-tail families, using
congruences at primes in the base. The fork's
`prime307_support_mitm.cpp` checks internal support cofactor
characters. The comparisons below concern specific projections
of the same swap equations. They assert no priority for using
partition reachability, and no lower bound for unrestricted #307.

## Uniform residue 1, modulo a prime square

Let ℓ be an odd prime and suppose every support prime is 1 modulo
ℓ. Write each as 1+ℓaₚ modulo ℓ². For a partition, let h,b be
the side sizes and X,Y the sums of the respective deviations
aₚ modulo ℓ. Put k=h+b and T=X+Y. Multiplication and reciprocation
give

- A=1+ℓX and B=1+ℓY modulo ℓ²
- U=h−ℓX and V=b−ℓY modulo ℓ²
- AU=h+ℓ(h−1)X and BV=b+ℓ(b−1)Y modulo ℓ²

The local swaps are therefore equivalent to h=b=1 modulo ℓ
and the two equations

```
(h−1)/ℓ = Y  (mod ℓ)
(b−1)/ℓ = X  (mod ℓ).
```

The first-order support condition is k=2+ℓT modulo ℓ², equivalently
C=2N modulo ℓ². Every partition has A²+B²=2N modulo ℓ², so this
is exactly the square-pair test restricted to products in the
principal-unit subgroup. It is also equivalent to the ambient
paired-square condition after k=2 modulo ℓ has been imposed.
Indeed C−2N is then divisible by ℓ and can be square modulo ℓ²
only if it vanishes, while C+2N reduces to the nonzero square 4.
Under this support condition either exact side swap implies the
other for the same partition.

**No further support-only exclusion at this modulus.** Suppose
the reciprocal mass is at least 2 and k is even, as required for
a solution supported on odd primes. The j-th smallest possible
support prime is at least 1+ℓj. If k≤2ℓ³, the mass is bounded by

```
H_(2ℓ³)/ℓ ≤ (1+log 2+3 log ℓ)/ℓ < 2.
```

For the last inequality, the numerator is less than 6 at ℓ=3
and its derivative is less than 2 for ℓ≥3. Hence k>2ℓ³ and some
one of the ℓ deviation classes occurs at least 2ℓ²+1 times.
Choose the first side solely from that class, with size
h=1+2ℓj for j=1,…,ℓ. Its deviation sum X stays fixed, whereas
(h−1)/ℓ runs through all residues modulo ℓ. Choose the value
matching Y=T−X. Both sides are odd and have at least three
members, and the support condition gives the other swap.

Fixed sizes can still obstruct. For example, modulo 9 take all
support primes 1 modulo 9 except one 4 modulo 9, and k=5 modulo
9. If h=7 modulo 9, the required complementary deviation is
2 modulo 3 while its only possible values are 0 and 1. The
paired-square and reciprocal-product checks pass with these sizes.

## Modulo 7, actual subset products versus the subgroup

Take k₀=5 modulo 7 regular primes of residue 1 and one exceptional
prime of residue 2. Then N=2, C/N=2 and C=4 modulo 7. The
ambient squares C+2N and C−2N are 1 and 0. The subgroup generated
by the support residues is {1,2,4}, and A=B=4 gives AB=2 and
A²+B²=4 there. Nevertheless no actual partition works. Its
products are 1 and 2 in some order, whose squares sum to 5.
The reciprocal-product screen passes by putting 1 modulo 7
regular primes on the first side. Each exact swap separately
has a witness, since putting 2 modulo 7 regular primes on
the first side gives A=1 and AU=2=B, and interchanging the
sides witnesses the other swap.

This separates subgroup and ambient squares from actual
multiplicative reachability. The multiplicative projection
alone already makes the rejection.

## Modulo 5, a genuinely coupled fixed-size rejection

Take k₀=3 modulo 5 regular primes of residue 1 and one exceptional
prime of each residue 2, 3 and 4. Fix a first-side size h=3
modulo 5 with 3≤h≤k₀. The complete table below specifies the
exceptional residues chosen on the first side. Fill its remaining
positions with regular primes. Here N=4, C/N=2 and C=3 modulo 5.
The four numerical columns are the two projected checks and
the errors in the two exact swaps.

| Exceptional residues chosen | A²+B² | UV | AU−B | BV−A |
|---|---:|---:|---:|---:|
| none | 2 | 2 | 4 | 0 |
| 2 | 3 | 0 | 3 | 2 |
| 3 | 3 | 2 | 4 | 1 |
| 4 | 2 | 1 | 3 | 2 |
| 2, 3 | 2 | 1 | 2 | 3 |
| 2, 4 | 3 | 2 | 1 | 4 |
| 3, 4 | 3 | 0 | 2 | 3 |
| 2, 3, 4 | 2 | 2 | 0 | 4 |

The actual subset-product screen, the reciprocal-product screen
and the two separate exact swaps all pass. No row passes the
two swaps together. The separation persists at arbitrarily
large reciprocal mass for the fixed size h=33. It does not show
an unrestricted heavy support rejected beyond multiplicative
reachability. At omitted modulus 5 the unrestricted distinction
in fact disappears once reciprocal mass is at least 2. The
first 30 primes have reciprocal sum less than 2, as the script
checks. Thus some residue class r contains more than 5d primes,
where d is the multiplicative order of r² modulo 5. Otherwise
the four classes would have at most 5, 10, 10 and 5 members.
For any attainable squared product x, hold the other classes
fixed and vary the selected count in class r while preserving
its residue modulo d. There are at least five consecutive
choices with step d. Their reciprocal contributions cover
the field, so one can attain U=N/x without changing A²=x.
If C=x+N²/x, this also gives V=x/N and both exact swaps.
The required residues U and V are nonzero, so both sides
are nonempty.
For an odd support and a product projection restricted to
odd side counts, the same conclusion preserves that parity.
The first 40 primes still have reciprocal sum below 2, so some
class has more than 10 members. Adjust its selected count by
multiples of 2, which preserves both parity and its squared
product and again covers the additive field.

For a concrete six-prime test, take {41,61,181,157,113,449}.
The script checks all internal cofactor squares and both 2-adic
paired squares. At 5 all odd-side partitions fail the joint
test. This small example has reciprocal mass below 2.

## Realizing the heavy examples

Use CRT to put all initial primes in the specified residue
classes and 1 modulo 512. Keep one exceptional prime for the
end. The ordinary class's reciprocal sum diverges, so one can
take as many as needed along the admissible size progression.

Let N₀ denote the product before appending the final prime r.
For each preceding prime p, prescribe the Legendre symbol
(r|p) equal to (N₀/p|p). Also prescribe r's needed exceptional
residue and r=1 modulo 512. CRT and Dirichlet's theorem supply
such a prime. All preceding cofactor symbols cancel. The final
one is +1 by quadratic reciprocity, since all primes are
1 modulo 4 and the product of the preceding conditions contains
each unordered pair's two reciprocal symbols.

Choose the total size k=66 modulo 512 as well as the indicated
size residue at the tested odd modulus. The two ambient 2-adic
square quantities are then 64 and 68 modulo 512. Their valuations
are 6 and 2 with unit parts 1 modulo 8, so both are squares
over the 2-adic integers. In the mod-5 example h=33 and its
complement are both 1 modulo 8, so the local swaps modulo 8
also pass. These are existence constructions for finite supports
of arbitrarily large mass, with no claim that they satisfy every
other local sieve.

Run `python3 check_local_sieves.py` to reproduce the finite
mod-7 and mod-5 residue checks and the concrete cofactor audit.
