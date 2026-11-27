# A056777 reduction to two bounded prime roots

The exact target is `OeisA56777.comesFromPrimeQuadruple_of_a.R2.H2.R1.H2`. The checked theorem `A056777.SmallPairs.exact_residual_of_pair_barrier` in `ReduceToPair.lean` shows that the following purely three-prime exclusion suffices.

Take primes p,a,b satisfying p≡3 mod 4, p≡2 or 3 mod 5, p≥23, 11<a<b<p, p²<a³ and 2ab<p². Exclude the divisibility
[
p^3\mid G(a,b),\qquad G(a,b)=a(a-1)b(b-1)+12(a+b-1).
]

This statement drops the original large root c, the other endpoint prime q, and the two arithmetic functions. The weakened pair conditions still suffice for the exact target.

## Why the pair constraint holds

Put u=ab and s=a+b−1. In the surviving orientation n=abc=p⁴q+12 the totient moment is
[
u+s(c-1)=p^3(p+q-1).
]
Multiply by u and substitute uc=p⁴q+12 to obtain
[
G(a,b)=u^2-us+12s=p^3[u(p+q-1)-pqs].
]
This identity applies to every pair of roots and retains the shift of 12 in the equality of the totients. Also, p·s−u is positive for a<p, so q is reconstructed exactly by dividing
[
q=\frac{u(p-1)-G(a,b)/p^3}{ps-u}.
]

For the ordered roots a<b<c, the checked moment identities imply a,b<p and c>p³. The evaluations of the doubled cubic used here are
[
F(p)=-p(q-1)(p^3-1)-2p^3(p-1)-24<0,
]
[
F(p^3)=-(q+1)p^5(p^3-1)-(q-1)p^6(p-1)-(q-1)p^3(p-1)-24<0.
]
The small-root existence follows from the pair sum being too small for all three roots to be at least p. Then F(p)<0 forces both smaller roots below p, and F(p³)<0 places c above p³. Since c is an integer, c≥p³+1, and abc=p⁴q+12 forces ab<pq because pq>12. The inherited inequalities q<a and p²<q³ imply p²<a³, while 2q<p gives 2ab<p².

## Strength of the modulus

For fixed p and a, there is at most one b in 0<b<p with the divisibility. If x<y were two, subtraction gives
[
p^3\mid (y-x)\,[a(a-1)(x+y-1)+12].
]
Cancel y−x, which is positive and below p. The bracket is even, strictly positive, and below 2p³. It cannot be the sole allowable positive multiple p³, which is odd.

Both the interval proof and the divisibility and uniqueness statements are checked in `SmallPairs.lean`. `ReduceToPair.lean` connects the pair exclusion to the exact upstream hypothesis. The Lean audits use only propext, Classical.choice and Quot.sound.

## Exact bounded scan

```sh
g++ -O3 -std=c++17 pair_scan.cpp -o pair_scan
./pair_scan 1000000
```

The scan solves the quadratic in b modulo p using a table of modular square roots. Every integer b with 0<b<p corresponds to one of at most two residues, so this is exhaustive in that range. It then checks the same quadratic modulo p³. The scan uses the relaxed bound 2a²<p², implied by a<b and 2ab<p². It found no p³ pairs for p≤1,000,000: 19,624 repeated primes, 545,267,582 first-root tests, and 28,088,531 ordered prime pairs passing modulo p. The run took about 86 seconds. This runtime check does not close the unrestricted Lean target.
