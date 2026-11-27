# A global size restriction from the first cubic root

In the surviving odd A056777 orientation, write the two endpoints as
\(m=p^4q\) and \(n=abc=m+12\), where \(a,b,c\) are distinct odd primes. Let \(F\)
be the doubled moment cubic. The previous root-location proof gives
\(q<\min(a,b,c)\). Since each root is odd, each is at least \(q+2\).
Consequently
\[
F(q+2)=2(q+2-a)(q+2-b)(q+2-c)\le0.
\]
Direct evaluation yields
\[
F(q+2)=4p^3(p-q-2)-(p^2+p)(q^3+4q^2+5q+2)+q^3+8q^2+17q-14.
\]

For \(q\ge107\), assume \(q^3\le3p^2\). Then \(p\ge5q\), and the leading
positive term is at least \(19p^4/6\). The opposing term is at most
\((101/100)(25/24)\cdot3p^4\), which is smaller. The final term is
nonnegative. This contradicts the required sign, so \(3p^2<q^3\).

The same calculation gives an asymptotic constant of four. For any
\(0<\varepsilon<4\), suppose an unbounded sequence of candidates has
\(q^3/p^2\le4-\varepsilon\). Then \(q/p\le 2/\sqrt q\to0\), and both \(p\)
and \(q\) tend to infinity. Dividing the displayed evaluation by \(p^4\)
and dropping the final nonnegative term gives
\[
\frac{F(q+2)}{p^4}
\ge 4\left(1-\frac qp-\frac2p\right)
-\left(1+\frac1p\right)\frac{q^3}{p^2}
 \left(1+\frac4q+\frac5{q^2}+\frac2{q^3}\right).
\]
The right side has lower limit at least \(\varepsilon\), a contradiction.
Thus along any unbounded sequence of candidates the lower limit of
\(q^3/p^2\) is at least four. This excludes a range near the old upper
bound on \(p\). It leaves parameters with \(p\) of order \(q\) untouched.
