# Simultaneous lifts at five odd composite moduli

At each \(M\in\{159,161,177,185,295\}\), let \(S\) be a finite set of distinct odd primes coprime to \(M\) with reciprocal mass at least 2. Start with any subset \(T\subseteq S\) and fix the placements of up to six primes as in \(T\). Every reciprocal sum in \(\mathbb Z/M\mathbb Z\) is attained by a subset that keeps those placements, the squared product of \(T\), and its cardinality parity. The subset works simultaneously at both prime factors of \(M\).

In particular, put \(N=\prod_{p\in S}p\) and \(C=N\sum_{p\in S}p^{-1}\), and suppose the starting partition has products \(A,B\) with \(A^2+B^2=C\pmod M\). Write \(x=A^2\) and prescribe the reciprocal sum \(N/x\) for the first side. In the resulting split with products \(A',B'\) and reciprocal sums \(U,V\), one has \((A')^2=x\), \(A'B'=N\), and \(V=C/N-U=x/N\). Thus \(A'U=B'\) and \(B'V=A'\) hold modulo \(M\). Fixing three primes on each side preserves the minimum side sizes. The quadratic hypothesis concerns one common starting partition.

## Independent binary choices

Let \(G=(\mathbb Z/M\mathbb Z)^{\times 2}\times\mathbb Z/2\mathbb Z\), write it additively, and let \(g_r=(r^2,1)\) for a unit residue \(r\). Start with the group subset-sum set \(A=\{0\}\). Whenever an unfixed prime with group contribution \(g\) has \(A+g\ne A\), reserve it and replace \(A\) by \(A\cup(A+g)\). At most \(|G|-1\) reservations occur. Every still-unreserved contribution belongs to the stabilizer \(H=\{h:A+h=A\}\), and every group target attainable from the unfixed primes lies in \(A\). Any family of choices on the unreserved primes whose group contribution is constant across its choices can therefore be compensated by a single choice of reserved primes.

For each pair of unit classes \(r,-r\) with unreserved populations \(m,n\), form as many mixed pairs as possible. Select exactly one from every mixed pair. Both possibilities give \(g_r\) and the reciprocal difference is \(2/r\), a unit modulo \(M\). The remaining primes are all in one class. Set \(d_r=\operatorname{ord}_G(g_r)\) and split these remaining primes into blocks of length \(d_r\), selecting all or none of each block. The group increment is zero and the reciprocal difference, up to sign, is \(d_r/r\). At the five certified moduli, \(\gcd(M,|G|)=1\). Since \(d_r\mid |G|\), every difference is a unit. The number of binary choices from the pair is

\[
q_r=\min(m,n)+\left\lfloor\frac{|m-n|}{d_r}\right\rfloor.
\]

Each unit generates the cyclic additive group modulo \(M\). Thus adjoining either of two values whose difference is a unit strictly grows a proper nonempty attainable set of reciprocal sums. At least \(M-1\) independent binary choices give all reciprocal sums, after one group compensation from the reserve.

## Integer mass bound

Suppose there are at most \(B=M-2\) binary choices. There are at most \(R=|G|-1+6\) reserved and fixed primes in total. Set \(K=10^{12}\) and \(L=300{,}000{,}000\), and write \(P_r(k)\) for the sum of the first \(k\) prime weights \(\lceil K/p\rceil\) in residue \(r\). Put

\[
F_r(k)=\max_{0\le i\le R}\{P_r(k+i)-Li\}.
\]

For a pair with \(q=q_r\) and \(s=\min(m,n)\), the larger unreserved population is at most \(t=s+d_r(q-s+1)-1\). If \(c\) fixed or reserved primes occur in the pair, its scaled mass is at most

\[
Lc+\max\{F_r(s)+F_{-r}(t),F_r(t)+F_{-r}(s)\}.
\]

This uses monotonicity of \(F_r\) and the optimality of the first eligible prime prefixes for bounding the mass. Subtract \(Lq\) and maximize the remaining bound independently over \(0\le s\le q\le B\) in each pair. Sum the per-pair maxima and add \(L(B+R)\). The result bounds the scaled reciprocal mass of every support with too few choices. The exact sieve verifies that every prefix used is complete.

| Modulus | Group order | Scaled upper bound for fewer than \(M-1\) choices |
| ---: | ---: | ---: |
| \(159=3\cdot53\) | 52 | 1,639,680,115,190 |
| \(161=7\cdot23\) | 66 | 1,841,035,381,514 |
| \(177=3\cdot59\) | 58 | 1,691,348,517,185 |
| \(185=5\cdot37\) | 72 | 1,753,851,992,730 |
| \(295=5\cdot59\) | 116 | 1,902,528,134,373 |

Each bound is strictly below \(2K\). Run `python simultaneous_lift_composite.py` for 295 or `python simultaneous_lift_composite.py --all` for the full table. These moduli extend the earlier simultaneous bounds through 150. [Earlier certificate](paired-mass.md)

Credit: Ali Hamdan via gpt-6.2-sol.
