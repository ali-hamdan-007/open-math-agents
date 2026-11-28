"""Finite scalar cases and nonnegative coefficient certificate for all r >= 3."""
import sympy as sy

r, k, x, y = sy.symbols("r k x y", real=True)
s = 3*r/2
N = (r+3)*k+1-r*(r+1)
u = (N-2*s+1)/(s+5)
v = (N-s+1)/(s+2)
f = lambda q: (q+1)*(2*k-3*q+1)-N-1
g = lambda b: (k-b+3)*b+k-b+1-N
tests = [(2*k-3)/3-u, f(k/2), f(u), g(k/2+1), g(v)]
for expr in tests:
    # Denominators depend only on positive factors 2, 3, s+2 and s+5.
    numerator = sy.fraction(sy.together(expr))[0]
    poly = sy.Poly(numerator.subs(k,3*r+2+x).subs(r,18+y).expand(), x, y)
    assert min(poly.coeffs()) > 0 and poly.eval({x:0,y:0}) > 0
    print(poly.as_expr())

big, small = [], []
for r in range(3,18):
    s = (3*r+1)//2
    for k in range(2*s+2,(4*r+12)*(s+5)):
        h = (k+1)//2
        N = (r+3)*k+1-r*(r+1)
        for q in range(h,(N-2*s+1)//(s+5)+1):
            if 3*q>2*k-3 or (q+1)*(2*k-3*q+1)<=N+1:
                big.append((r,k,q))
        for b in range(h+1,min(k-1,(N-s+1)//(s+2))+1):
            if (k-b+3)*b+k-b+1<=N:
                small.append((r,k,b))
assert big == [(4,20,10)], big
assert small == [(3,12,8),(4,14,8),(4,14,9),(4,15,10)], small
print("big",big,"small",small)
