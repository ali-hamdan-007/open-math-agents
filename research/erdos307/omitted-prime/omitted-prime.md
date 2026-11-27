# Erdős 307 omitted-prime congruence

Let \(S\) be the prime support, \(N=\prod_{p\in S}p\), and \(C=\sum_{p\in S}N/p\). The cross-product equalities give \(N=AB\) and \(C=A^2+B^2\), where \(A,B\) are the products of the two sides. For an odd prime \(\ell\notin S\), reduce these quantities modulo \(\ell\). In particular, \(N\ne0\) in \(\mathbb F_\ell\).

## Exact paired-square test

Local values \(a,b\in\mathbb F_\ell\) with \(ab=N\) and \(a^2+b^2=C\) exist exactly when both \(C+2N\) and \(C-2N\) are squares, with zero allowed. Necessity follows from \((a\pm b)^2=C\pm2N\). For sufficiency, choose any roots \(u^2=C+2N\) and \(v^2=C-2N\), and set \(a=(u+v)/2\), \(b=(u-v)/2\). Then \(ab=(u^2-v^2)/4=N\) and \(a^2+b^2=(u^2+v^2)/2=C\). Both \(a\) and \(b\) are nonzero because \(N\ne0\). Either square may vanish, but both cannot vanish because their difference is \(4N\). No choice of signs requires coordination.

The test thus takes two Legendre evaluations or fewer with short circuiting. A Legendre value of 0 passes along with +1. This is exactly the local version of Bonfioli's existing paired-square sieve on the two Pythagorean layers. Checking finitely many primes is a modular screen for the integer conditions, and is not a test for integer squares or witnesses.

## Equivalent Dickson recurrence

Define \(D_0=2\), \(D_1=C\), and \(D_{j+2}=C D_{j+1}-N^2D_j\). The power-sum identity gives \(D_j=a^{2j}+b^{2j}\). Fermat's little theorem yields the support-only equation \(D_{(\ell-1)/2}=2\). Lean verifies this necessity in the general theorem and specializes it to \(C^2-2N^2=2\) at 5 and \(C^3-3N^2C=2\) at 7.

Conversely, let \(x,y\) be the two roots of \(T^2-CT+N^2\) in \(\mathbb F_{\ell^2}\), counted with multiplicity, and put \(k=(\ell-1)/2\). They are nonzero and satisfy \(x^ky^k=N^{\ell-1}=1\). If \(D_k=2\), then \(x^k+y^k=2\), so \(x^k=y^k=1\). Consequently \(x,y\) lie in the subgroup of nonzero squares of \(\mathbb F_\ell\), which consists of all \(k\) roots of \(T^k-1\). Choose \(a^2=x\) with \(a\in\mathbb F_\ell\) and set \(b=N/a\). Then \(ab=N\) and \(a^2+b^2=C\). This converse is a paper argument.

With \(z=N^2\), the doubling rules are \(D_{2j}=D_j^2-2z^j\), \(D_{2j+1}=D_jD_{j+1}-Cz^j\), and \(D_{2j+2}=D_{j+1}^2-2z^{j+1}\). Updating \(D_j,D_{j+1},z^j\) consumes \(O(\log\ell)\) field operations. These formulas provide an equivalent presentation of the paired-square screen with the same rejection set.

The support \(\{2,3,23\}\) demonstrates the distinction between the paired-square screen and the separate internal cofactor-square checks. Its internal checks give 1 at 2 and 3, and the cofactor 6 at 23 is \(11^2\bmod23\). Yet \(N=138\) and \(C=121\) give \(C^2-2N^2\equiv3\bmod5\). For examples of arbitrary cardinality along a sequence, append primes \(r\equiv1\bmod 40N\) successively, where \(N\) is the previous product. Dirichlet supplies each prime. The internal checks persist by quadratic reciprocity and the supplementary law at 2. Modulo 5, the product stays fixed and the cofactor sum increases by \(N\) per appended prime. After any multiple of five additions, the same rejection holds. These examples do not impose the reciprocal-mass lower bound.
