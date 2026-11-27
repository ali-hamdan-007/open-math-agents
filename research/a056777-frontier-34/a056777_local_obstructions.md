# Local solvability of the remaining A056777 cubic

Write
\[
h_p=p^2+p+1,\qquad
T_p(x)=h_px^2-(2p^3+h_p)x+2p^4,\qquad
B_p(x)=2x^3-(h_p+2p^3)x^2+(2p^4+h_p-2)x-24.
\]
The doubled moment cubic is \(F_{p,q}(x)=B_p(x)-qT_p(x)\). Its half is a monic integer cubic for odd integral \(p,q\). The remaining branch requires three distinct prime roots and the congruences \(p\equiv3\bmod4\), \(q\equiv3\bmod8\), \(p\not\equiv q\bmod3\), \(p\equiv2,3\bmod5\), and \(q\equiv2\bmod5\).

**Local conclusion.** For every prime \(\ell\), there are units \(p,q\in\mathbb Z_\ell\) for which the moment cubic factors into three distinct \(\ell\)-adic unit roots, respecting the displayed congruences at \(2,3,5\). Consequently every fixed modulus has unit residue solutions to the moment equations and to their resultant identities. The exact integer divisor condition and global primality can still impose further constraints.

## The curve governing splitting

Fix \(p\) in a field of odd characteristic and put
\[
G_p(x,y)=\frac{B_p(x)T_p(y)-B_p(y)T_p(x)}{x-y}.
\]
The numerator vanishes at \(y=x\), so \(G_p\) is a polynomial of degree at most two in each variable. Its leading coefficient in \(y\) is \(2T_p(x)\). If \(T_p(x)\ne0\) and \(q=B_p(x)/T_p(x)\), then \(G_p(x,y)=T_p(x)F_{p,q}(y)/(y-x)\). A root of the quadratic therefore supplies another root of \(F_{p,q}\).

At \(p=1\) the quadratic is
\[
G_1(x,y)=(6x^2-10x+4)y^2+(-10x^2+20x+62)y+4x^2+62x-114.
\]
Its discriminant in \(y\) is \(4W(x)\), where
\[
W(x)=x^4-432x^3+1078x^2-768x+1417,\qquad
\operatorname{disc}(W)=-2^{16}3^3 11^3 29^3\cdot25841.
\]
For odd \(\ell\nmid\operatorname{disc}(W)\), the smooth projective model of \(z^2=W(x)\) has genus one. The degree-two map to the \(x\)-line has four simple branch points and is unramified at infinity. At most two points lie over infinity, so the Hasse–Weil bound gives at least \(\ell-1-2\sqrt\ell\) affine points. [Stoll, Arithmetic of hyperelliptic curves, Theorem 3.12](https://www.mathe2.uni-bayreuth.de/stoll/teaching/ArithHypKurven-SS2019/Skript-ArithHypCurves-pub-screen.pdf)

Discard \(x=0\), the roots of \(T_1(x)=0\), and the roots of \(B_1(x)=0\) or \(B_1(x)+12T_1(x)=0\). This removes at most nine values of \(x\) and ensures \(q\ne0,-12\). The discriminant in \(x\) of \(F_{1,q}(x)\) is
\[
9q^4-2572q^3+22q^2-2572q-61239.
\]
Discard its at most four roots \(q\) and the at most three roots \(x\) corresponding to each. At most 21 values of \(x\) are discarded in total, each accounting for at most two points of the quartic. For \(\ell\ge61\) we have \(\ell-1-2\sqrt\ell>42\). Thus one point survives with \(T_1(x)\ne0\), nonzero \(q\), and a separable cubic. It supplies two roots and therefore all three. The constant term is nonzero since \(q\ne-12\), so all three roots are units. Simple-root Hensel lifting gives the claimed \(\ell\)-adic factorization.

The companion script checks witnesses for the 18 excluded primes, the primes below 61 and 25841. At \(2\) and \(3\) it verifies the strengthened Hensel hypothesis \(v_\ell(f(t))>2v_\ell(f'(t))\) with disjoint root neighborhoods. At all other excluded primes it checks ordinary simple-root witnesses. For any fixed modulus, combine the local data by the Chinese remainder theorem. Use one extra bit for \(p,q\) at 2 to account for halving the coefficients. If a modulus does not contain \(2,3,5\), include these congruences in the Chinese remainder step as well.

## Most residues of \(p\) modulo a large prime are admissible

The argument is uniform in the residue of \(p\) outside a bounded number of exceptions. Let \(D_p(x)\) be the discriminant of \(G_p(x,y)\) in \(y\). It has degree at most four in \(x\). All coefficients of \(G_p\) have degree at most eight in \(p\), so the coefficients of \(D_p\) have degree at most sixteen in \(p\). Let \(d(p)\) be the \(x^4\) coefficient of \(D_p\) and \(e(p)\) the polynomial discriminant of that quartic in \(x\). The degrees of \(d\) and \(e\) are at most 16 and 96, since the quartic discriminant is homogeneous of degree six in its coefficients. At \(p=1\) they are nonzero modulo every prime outside \(2,3,11,29,25841\).

For such a prime \(\ell\ge61\), discard the at most \(115\) roots of \(ph_pd(p)e(p)=0\). For any other \(p\) residue, \(D_p\) is a squarefree quartic and the same affine point bound applies to \(z^2=D_p(x)\). The leading coefficient \(d(p)\) is \(4\operatorname{disc}(T_p)\), by comparing the coefficients of \(x^2\) in \(G_p\). The coefficient of \(q^4\) in the discriminant of \(F_{p,q}(x)\) in \(x\) is \(h_p^2\operatorname{disc}(T_p)\), by the cubic discriminant formula. Both are therefore nonzero. In the counting argument discard \(q=-12/p^4\) in place of \(q=-12\), and the other exclusions have the same bounds. This local test admits at least \(\ell-115\) residue classes of \(p\). The bound concerns one modulus prime at a time. It leaves open constraints that use the size and exact divisors of the integer \(T_p(x)\), or a modulus that grows with the parameters.
