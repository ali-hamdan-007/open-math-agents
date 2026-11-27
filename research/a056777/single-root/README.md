# A056777 unbounded single-root step

The reduction in `lint/reductions/OeisA56777.comesFromPrimeQuadruple_of_a.R2.H2.R1.H2.R1.H2.R1.lean` targets the existing isolated H2. It splits into the two allowed residue classes of the repeated prime $p$ modulo five. The project requires two to four hypotheses for a reduction.

At an isolated root $x$, the doubled cubic is $F=p^2G-xE-24$, where

$$
G=-(2p+q)x^2+2p(p+q)x-2p^2q,\qquad
E=p^2(x-q-1)+(p+1)(q+1)(x-1)-2x^2+2.
$$

The existing interval $q+4\le x<p$ makes $E>0$. Therefore $G>0$ at a root. Completing the square gives $p^2>2pq+q^2$.

Residues modulo three rule out $x-q\equiv1\pmod3$, which excludes gaps four and ten. In the $p\equiv2\pmod5$ branch, evaluating the cubic modulo five excludes gap six, and primality excludes gap eight. Thus this branch starts at gap twelve.

The one-root cubic also gives three congruence refinements. If $q\equiv1\pmod3$, then $q\equiv4\pmod9$ and $x\equiv1\pmod3$. If $q\equiv2\pmod3$ and $x\equiv1\pmod3$, then $p\equiv7\pmod9$. If $p\equiv2\pmod5$ and $x\equiv1\pmod5$, then $q\equiv12\pmod{25}$.

Both new hypotheses remain unresolved. The isolated target carries one root. The separate `Sharpened.lean` experiment uses the three roots available in the preceding reduction, so its unconditional $11p^2<q^3$ and conditional $22p^2<q^3$ bounds do not appear in the isolated connector.
