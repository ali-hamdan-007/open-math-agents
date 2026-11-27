# Independent review of the A056777 prime-root divisor reduction

The imported parent is byte-for-byte the merged #5561 source, Git blob `f44b5ff0c4d692543066955a5dc3285bc31b94da`. Its H2 is the squarefree three-factor endpoint exactly 12 above $p^4q$ with the additive totient and divisor-sum equalities and the indicated prime congruences. The local main theorem has only the standard Lean axioms in its focused audit. The two child hypotheses exhaust $q<4000$ and $q\ge4000$. [Merged parent #5561](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5561)

For distinct prime factors $a,b,c$ of the upper endpoint, the totient and divisor-sum formulas give
$$
L=2(a+b+c)=(p^2+p+1)(q+1)+2p^3,
\qquad
M=2(ab+ac+bc)=2p^3(p+q-1)+L-2.
$$
Since $abc=p^4q+12$, each prime factor is an integer root of $F(X)=2X^3-LX^2+MX-2(p^4q+12)$. The compiled lemmas produce a prime root $q<x<p$, the indicated $q+4$ or $q+6$ spacing, and, for $q\ge4000$, the stricter $7p^2<q^3$ and conditional $11p^2<q^3$ bounds. The recovery equation in each child is $F(x)=0$ upon expanding $T$. The product identity makes $T(x)$ a divisor of an integer depending only on $p$; positivity gives a genuine reconstruction of $q$. Thus the reduction uses an exact polynomial relation and additional restrictions, while dropping the requirement that the other roots are distinct primes.

## Finite check for H1

Run `python /tmp/a56nov28/review_search.py`. For each prime $q<4000$ with $q\equiv27\pmod{40}$, check primes $p$ with the exact congruences and $2q<p<\sqrt{q^3}$. Set the interval for $x$ using the exact lower spacing and strict $x<p$. The cubic first difference is
$$
F(x+1)-F(x)=6x^2+(6-2L)x+2-L+M.
$$
It strictly decreases across the interval, since its successive difference is $12x+12-2L<0$. An exact integer binary search finds where the first difference changes sign, then checks for a zero in each of the two monotone integer intervals. The exact run considered 33,817 prime pairs and found zero integer roots. This proves absence of numerical H1 witnesses in the external checker. The search implementation and its completeness have not been checked in Lean.

An exploratory run with `15000` as the exclusive $q$-bound checked 255,238 prime pairs after applying the corresponding H1 or H2 filters. It found zero integer roots. The finite run does not prove the unbounded H2.

## Strengthening H2 after the split

If an enhanced divisor-root reduction is useful, retain the positive-square discriminant for the other two roots. With $S=L/2$ and $N=p^4q+12$, dividing the cubic relation by the prime root gives the monic quadratic
$$
Y^2-(S-x)Y+N/x=0.
$$
In a parent candidate the other two roots are the remaining prime factors $a,b$, so the discriminant is $(a-b)^2>0$. The strongest exact reconstruction additionally checks that both roots are primes with the inherited spacing, and distinct from $x$ as well as from each other. This eliminates the logical possibility of extraneous one-root candidates without losing the divisor-first structure. No actual spurious H2 solution was found in the audited range. A useful order after parent merge is to close finite H1 with a kernel-checked search, then use whichever H2 reconstruction predicate materially helps the unbounded analysis.
