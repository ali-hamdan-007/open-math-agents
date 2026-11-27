# Prescribed squared-product lifts at omitted primes

Let \(S\) be a finite set of distinct odd primes omitting the odd prime \(\ell\). Let \(T\subseteq S\), and fix the placements of at most six primes as in \(T\). If \(\sum_{p\in S}1/p\ge 2\), then every element of \(\mathbb F_\ell\) occurs as the reciprocal sum of a subset respecting the placements and having the same cardinality parity and squared product as \(T\), for **every odd prime \(\ell\le181\)**. The argument gives a general criterion for other odd primes and any allowance for fixed placements. The earlier paired-class proof covers every odd prime through 53 and the additional moduli 61 and 73. [Earlier certificate](paired-mass.md)

## Reserving primes for the product and parity

Write \(G=\mathbb F_\ell^{\times 2}\times\mathbb Z/2\mathbb Z\) additively, and let \(g_r=(r^2,1)\) be the contribution of residue \(r\). Start with \(A=\{0\}\). Reserve an unfixed prime \(p\) whenever \(A+g_p\ne A\), replacing \(A\) with \(A\cup(A+g_p)\). Stop when every unreserved unfixed prime stabilizes \(A\). Each reservation grows \(A\), so at most \(|G|-1=\ell-2\) primes are reserved. The final \(A\) is the set of all subset sums of the reserve. Every sum of unreserved contributions belongs to the stabilizer \(H=\{h:A+h=A\}\).

The product and parity target from \(T\) after the fixed placements have been accounted for belongs to \(A\). If choices on unreserved primes all give the same contribution \(h\), that contribution lies in \(H\), and one selection from the reserve supplies the target minus \(h\). This works for every attainable starting product and parity. If the unfixed contributions generate a subgroup of order \(u\), the reservation count improves to \(u-1\).

## Independent choices for the reciprocal sum

For each opposite pair of residues \(r,-r\), pair as many primes from opposite classes as possible. Select exactly one prime in each pair. These mixed choices have the same group contribution \(g_r\), and their reciprocal sums differ by \(2/r\) up to sign. The leftover primes from an opposite pair are all in one residue class. Write \(d_r=\operatorname{ord}_G(g_r)=\operatorname{lcm}(2,\operatorname{ord}(r^2))\).

Group the opposite residue pairs into orbits of inversion, so \(\{r,-r\}\) is grouped with \(\{r^{-1},-r^{-1}\}\). If the two pairs are distinct, their group contributions are negatives of one another. Match as many leftover primes from the two pairs as possible, selecting both or neither in each match. Each such choice contributes zero in \(G\). Its reciprocal change is \(1/x+1/y\) for residues \(x,y\) in the two distinct opposite pairs. This change is nonzero since the two pairs are disjoint, and thus \(y\ne -x\). This leaves one residue class with leftover primes. Divide these into blocks of length \(d_r\), again selecting all or none in each block. These choices contribute zero in \(G\) and have a nonzero reciprocal change since \(d_r\mid\ell-1\). For a single opposite pair fixed by inversion, go straight from the mixed choices to the same-residue blocks.

For a nontrivial inversion orbit, let \(s_1,s_2\) be the mixed-choice counts and \(X,Y\) the respective populations after those choices have been formed. The number of binary choices in the orbit is

\[
q=s_1+s_2+\min(X,Y)+\left\lfloor \frac{|X-Y|}{d_r}\right\rfloor.
\]

In a one-pair orbit the corresponding count is \(q=s+\lfloor X/d_r\rfloor\). Across all the choices, the group contribution of the selected unreserved primes is constant. A single selection of the reserve therefore makes every choice respect the group target. Each binary choice adds a two-point set to the attainable reciprocal sums. A nonzero translation generates \(\mathbb F_\ell\) under addition, so each such addition grows the attainable set unless it is already full. Thus \(\sum q\ge\ell-1\) gives every reciprocal sum.

## Integer reciprocal-mass certificate

Set \(B=\ell-2\) and \(R=\ell-2+f\), where \(f\) is the allowance for fixed placements. If the choices above do not suffice, their total is at most \(B\), and the total number of fixed and reserved primes is at most \(R\). Let \(K\) be a positive integer and let \(P_r(k)\) be the sum of the rounded-up weights \(\lceil K/p\rceil\) of the first \(k\) eligible primes in residue \(r\). For an integer penalty \(L\ge0\), put

\[
F_r(k)=\max_{0\le i\le R}\bigl(P_r(k+i)-Li\bigr).
\]

If a residue has \(k\) unreserved and \(i\) fixed or reserved primes, its scaled reciprocal mass is at most \(F_r(k)+Li\). Each \(F_r\) is nondecreasing. For an opposite pair and integers \(x,c\ge0\), define

\[
M_r(x,c)=\max_{0\le s\le c}\Bigl(
\max\{F_r(s)+F_{-r}(s+x),F_{-r}(s)+F_r(s+x)\}-Ls\Bigr).
\]

For a one-pair orbit a bound on the scaled mass minus \(L\) times the number of choices and the number fixed or reserved is

\[
\max_{0\le b\le B}\bigl(M_r(d_r(b+1)-1,B-b)-Lb\bigr).
\]

Here \(b\) counts same-residue blocks, so the excess population outside the mixed choices is at most \(d_r(b+1)-1\). For a two-pair orbit with representatives \(r,t\), let \(v=\min(X,Y)\), \(b=\lfloor|X-Y|/d_r\rfloor\), \(c=B-v-b\), and \(z=v+d_r(b+1)-1\). One leftover population is exactly \(v\) and the other is at most \(z\). Each of the mixed-choice counts is at most \(c\). A bound on the same penalized quantity is

\[
\max_{\substack{v,b\ge0\\v+b\le B}}
\Bigl(\max\{M_r(z,c)+M_t(v,c),M_t(z,c)+M_r(v,c)\}-L(v+b)\Bigr).
\]

Maximizing the two mixed-choice counts independently only increases the bound. Sum the per-orbit bounds and add \(L(B+R)\) to bound the total scaled reciprocal mass. The sieve asserts it has all prime prefixes used. The verifier maximizes each \(M_r\) by checking both orientations and locating where increasing \(s\) ceases to help. This works because \(F_r\) is discretely concave. As \(k\) increases, its successive differences go through three regimes determined by how many prime weights exceed \(L\): the declining weights at positions \(k+R+1\), the constant increment \(L\), and the declining weights at positions \(k+1\). Regimes can be empty.

With \(K=10^{12}\), \(L=500{,}000{,}000\), and \(f=6\), representative scaled bounds are as follows. The upper bound is strictly below \(2K\) for each of the 33 odd primes through 139. The same test with \(L=450{,}000{,}000\) also certifies 149, 151, and 157.

| Omitted prime | Scaled mass upper bound |
| ---: | ---: |
| 59 | 1,868,715,043,441 |
| 67 | 1,872,115,564,086 |
| 71 | 1,878,800,918,624 |
| 83 | 1,910,700,346,814 |
| 103 | 1,932,289,872,165 |
| 107 | 1,952,126,888,080 |
| 127 | 1,962,956,804,555 |
| 131 | 1,971,677,167,225 |
| 139 | 1,986,266,937,793 |
| 149 | 1,989,238,996,898 |
| 151 | 1,992,926,193,872 |
| 157 | 1,988,539,824,517 |

Run `python parity_lift_prime.py` to reproduce the 67 certificate, or `python parity_lift_prime.py --all` to replay the complete range.

## Faster reservations inside a cyclic subgroup

Let \(d\) be the greatest order of any \(g_r\). Group the inversion orbits of order \(d\) by the subgroup \(J=\langle g_r\rangle\) they generate. Within \(J\), each orbit represents a generator direction \(\{g,-g\}\). Suppose one such subgroup has at least \(d/2\) unfixed generator primes outside every single direction among its own generator primes. Then while at most \(d/2-1\) primes have been reserved, at least two directions remain in that subgroup.

For a subset \(A\subseteq J\) with \(2\le |A|\le d-2\), growth by one upon adding an option \(g\) requires \(A\) to be an interval in the cyclic order generated by \(g\). Indeed \(|(A+g)\setminus A|\) counts the ends of the runs along that order. For an interval of length \(k\), a shift by \(tg\) adds \(\min(k,d-k,t,d-t)\) elements for \(0\le t<d\). To see this, one can replace the interval by its complement and negate the shift so that both \(k\) and \(t\) are at most \(d/2\), and then count the overlap directly. Consequently two distinct directions cannot both give growth by one. After reserving one generator, choose a prime of growth at least two while the attainable set has size at most \(d-2\). At size \(d-1\), any remaining generator fills the last point. At most \(d/2\) reservations fill \(J\). Use the initial greedy argument in \(G/J\) to reserve at most another \(|G|/d-1\) primes. The same mass certificate then uses \(R=f+d/2+|G|/d-1\).

In the remaining case, each of the cyclic subgroups has a direction with at most \(d/2-1\) unfixed generator primes outside it within that subgroup. Including fixed placements, the outside directions in each subgroup contain at most \(d/2-1+f\) primes. For each possible choice of the retained direction, sum its usual penalized bound and the largest eligible reciprocal weights for the outside primes in the subgroup. Take the maximum over retained directions independently for each subgroup. The directions of order less than \(d\) use the usual bound. Add \(L(B+R)\) with the original \(R=\ell-2+f\). Omitting the penalties on the directly bounded outside primes increases the resulting upper bound.

| Omitted prime | Bound with faster reservations | Bound with few outside primes |
| ---: | ---: | ---: |
| 163 | 1,976,862,210,857 | 1,868,218,744,822 |
| 167 | 1,993,475,015,074 | 1,748,596,380,450 |
| 173 | 1,961,573,337,158 | 1,785,518,501,559 |
| 181 | 1,953,141,416,671 | 1,941,771,889,744 |

## Nineteen distinct squared residues at 179

The order of the square group at \(\ell=179\) is the prime 89. If the unfixed primes occupy at least 19 distinct squared-residue classes, reserve one prime from each of any 19 such classes and take their distinct square-group logarithms in \(\mathbb F_{89}\). The Dias da Silva–Hamidoune bound for sums of \(k\) distinct members of a set of size 19 gives at least \(\min(89,k(19-k)+1)\) attainable logarithms. This is 89 for both \(k=8\) and \(k=9\), so the reserved primes supply every combination of squared product and parity. The mass bound with \(R=19+6\) is \(1{,}973{,}320{,}224{,}830\). [Hou and Sun, *Restricted sums in a field*, equation (1.1)](https://www.impan.pl/shop/en/publication/transaction/download/product/83841)

In the other case at most 18 ordinary opposite pairs contain any unfixed primes. The verifier goes through the inverse directions, tracking the number of active ordinary opposite pairs and the number of fixed primes in inactive pairs. The bound for two active pairs is the usual inverse-direction bound. For one active pair it adds the active pair's ordinary bound to the inactive pair's maximum exact fixed-only prefix weight minus the reservation penalty. With no active pairs it combines the two fixed-only bounds. The order-2 pair uses the usual bound without occupying an ordinary slot. Maximizing over at most 18 ordinary slots and at most six fixed-only primes gives \(1{,}576{,}711{,}291{,}747\), with the same global choice and reservation penalties as before. Both bounds use \(L=450{,}000{,}000\).

## A cardinality criterion and a limitation

For any odd \(\ell\), \(\ell(\ell-1)-1\) unfixed primes suffice without a reciprocal-mass hypothesis. Track subset sums of \((g_p,1/p)\) in \(G\times\mathbb F_\ell\). Every individual contribution generates a subgroup containing \(\{0\}\times\mathbb F_\ell\) since multiplication by \(|G|=\ell-1\) annihilates its group component and leaves a nonzero field component. Until the attainable set is invariant under all vertical translations, each new contribution strictly enlarges it. Starting from one element, \(\ell(\ell-1)-1\) strict increases would fill the entire set, which is vertically invariant. Invariance is preserved by all later additions.

A reciprocal-mass threshold of 2 cannot work uniformly over every odd prime. For any fixed finite support of odd primes of mass at least 2 and product \(N\), choose \(\ell>2N\). If two subsets have products \(a,b\) with \(a^2=b^2\pmod\ell\), then \(\ell\) divides \(a-b\) or \(a+b\). Both products are in \([1,N]\), so \(a=b\), and unique factorization gives the same subset. Each squared-product fiber therefore yields only one reciprocal sum in these moduli.

## Application to Erdős 307

Put \(N=\prod_{p\in S}p\) and \(C=\sum_{p\in S}N/p\). Suppose a starting subset has side products \(A,B\) with \(A^2+B^2=C\) modulo \(\ell\). Keep the squared product \(x=A^2\) and prescribe the new first side's reciprocal sum to be \(U=N/x\). If \(A',B'\) are the new side products, then \((A')^2=x\), \(A'B'=N\), and the second side's reciprocal sum is \(V=C/N-U=x/N\). Thus \(A'U=B'\) and \(B'V=A'\) modulo \(\ell\). Fixing three primes per side preserves the side size lower bound of three. Each application produces a partition for one omitted prime from an attainable squared-product witness.

Credit: Ali Hamdan via gpt-6.2-sol.
