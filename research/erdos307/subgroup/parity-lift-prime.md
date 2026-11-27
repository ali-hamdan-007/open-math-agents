# Prescribed-product lifts at omitted primes

Let \(S\) be a finite set of distinct odd primes omitting the odd prime \(\ell\). Let \(T\subseteq S\), and fix the placements of at most six primes as in \(T\). For \(\ell=67\), if \(\sum_{p\in S}1/p\ge 2\), then every element of \(\mathbb F_{67}\) occurs as the reciprocal sum of a subset respecting those placements and having the same parity and squared product as \(T\). The criterion below applies to any odd prime and any allowance for fixed placements.

## Reserve primes by strict growth

Write \(G=\mathbb F_\ell^{\times 2}\times\mathbb Z/2\mathbb Z\) additively, and let \(g_p=(p^2,1)\) denote the contribution of prime \(p\) in \(G\). Starting with \(A=\{0\}\), reserve an unfixed prime \(p\) whenever \(A+g_p\ne A\), and replace \(A\) by \(A\cup(A+g_p)\). Stop when every unreserved unfixed prime stabilizes \(A\). Each reservation grows \(A\) by at least one. Since \(|G|=\ell-1\), at most \(\ell-2\) primes are reserved. At termination \(A\) is the set of all subset sums of the reserve, and every sum of unreserved contributions belongs to the stabilizer \(H=\{h:A+h=A\}\). The product and parity target from \(T\), after removing the fixed elements, therefore belongs to \(A\).

Choose independently among pairs or blocks of unreserved primes as follows. For each opposite pair of residues \(r,-r\) with populations \(m,n\), form \(\min(m,n)\) mixed pairs and select exactly one prime from each pair. Each such choice contributes \(g_r\) in \(G\), and its two reciprocal sums differ by \(2/r\) up to sign. Split the remaining primes in the more numerous residue into blocks of length \(d_r=\operatorname{ord}_G(g_r)=\operatorname{lcm}(2,\operatorname{ord}(r^2))\) and select all or none of each block. Their contributions in \(G\) are zero and their two reciprocal sums differ by \(d_r/r\) up to sign, which is nonzero because \(d_r\mid \ell-1\). Leave the remainder in the complement. This gives

\[
q_r=\min(m,n)+\left\lfloor \frac{|m-n|}{d_r}\right\rfloor
\]

independent choices in this residue pair. The total contribution in \(G\) of the selected unreserved primes is a fixed \(h\in H\) across all choices. A single selection from the reserve can supply the target minus \(h\). Each binary choice adds a two-point set to the attainable reciprocal sums. A nonzero translation generates \(\mathbb F_\ell\) under addition, so each such sumset addition grows the attainable set unless it is already full. Thus \(\sum_r q_r\ge\ell-1\) gives every reciprocal sum.

This proof also explains what happens when the unfixed residues generate a proper subgroup of \(G\), or generate \(G\) but realize only some subset sums. The argument needs the attainable set \(A\) and its stabilizer. In particular, if the unfixed contributions generate a subgroup of order \(h\), the reservation count improves to \(h-1\).

## Mass certificate

Set \(B=\ell-2\) and \(R=\ell-2+f\), where \(f\) is the number of placements allowed. The only case left to bound has \(\sum_r q_r\le B\). Let \(K\) be a positive integer, and let \(P_r(k)\) sum the rounded-up weights \(\lceil K/p\rceil\) of the first \(k\) eligible primes congruent to \(r\). With an integer penalty \(L\ge0\), define

\[
F_r(k)=\max_{0\le i\le R}\bigl(P_r(k+i)-Li\bigr).
\]

For an opposite pair with \(s=\min(m,n)\) and \(q=q_r\), its larger unreserved population is at most \(b=s+d_r(q-s+1)-1\). If \(c\) primes in the pair are fixed or reserved, the scaled reciprocal mass in the pair is at most

\[
Lc+\max\{F_r(s)+F_{-r}(b),F_r(b)+F_{-r}(s)\}.
\]

In fact the weight of each class is at most its prime-prefix weight, and \(F_r\) is nondecreasing because all \(P_r\) are. Subtract \(Lq\) from the displayed maximum, maximize over \(0\le s\le q\le B\) independently for each residue pair, sum the resulting bounds, and then add \(L(B+R)\). This gives an integer upper bound for the scaled reciprocal mass whenever the binary choices do not suffice.

For \(\ell=67\) use \(K=10^{12}\), \(L=700{,}000{,}000\), \(B=65\), and \(R=71\). The scaled bound is \(1{,}939{,}806{,}948{,}835<2K\). Run `python parity_lift_prime.py` to reproduce it. The verifier asserts that the integer sieve produces every prime prefix used in the proof.

Without the weighted certificate there is also a cardinality criterion for any odd prime. In the case \(\sum_r q_r\le\ell-2\), each pair has total unreserved population at most \(d_r(q_r+1)-1\). Consequently a lift exists once

\[
|S| > f + (\ell-2) + (\ell-1)(\ell-2) + \sum_{r=1}^{(\ell-1)/2}(d_r-1).
\]

## Application to Erdős 307

Put \(N=\prod_{p\in S}p\) and \(C=\sum_{p\in S}N/p\). Suppose the starting partition has side products \(A,B\) with \(A^2+B^2=C\) modulo \(\ell\). Keep the squared product \(x=A^2\) and prescribe the first side's reciprocal sum to be \(U=N/x\). With \(V=C/N-U\) on the second side, the construction gives \(V=x/N\), \(AU=B\), and \(BV=A\) modulo \(\ell\). Fixing three primes per side preserves the side size lower bound of three. This certifies a local partition at the chosen prime from an attainable squared-product witness.

Credit: Ali Hamdan via gpt-6.2-sol.
