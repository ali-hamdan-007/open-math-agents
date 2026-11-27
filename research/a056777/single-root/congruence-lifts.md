# Local restrictions for the first child of #9935

Write F for the right-hand side of the cubic identity minus qT. Assume p and q are both 2 modulo 5. In the x=1 modulo 5 branch, the parent forces q=12 modulo 25. Write p=2+5v, q=12+25w and x=1+5u. The condition F=0 modulo 125 gives u²+(v−1)u+v²+3v+w+3=0 modulo 5. Its discriminant is 2(v−1)²+w+2 modulo 5. Fifteen of the 25 possible (v,w) classes survive. The executable also checks the next q lift in the double-root case.

With p=3+4a and q=3+8b, substitution gives F(p,q,1+4c)=16(a+1) and F(p,q,3+4c)=16b modulo 32. The full mod-64 enumeration leaves 80 out of 128 admissible pairs of residue classes with an odd cubic root.

For distinct odd primes p,q,x in the specified range, divisibility of p⁴q+12 by x implies the Legendre symbol (q/x)=(-3/x). Since q=3 modulo 4, quadratic reciprocity yields (x/q)=(3/x). The script checks the example p=50207, q=4027, where the cubic root modulo q has the wrong quadratic character for every allowable x. The other unbounded cases remain open. See congruence_lifts.py for the complete polynomial and exact tests.
