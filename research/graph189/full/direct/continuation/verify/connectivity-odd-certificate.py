"""Odd r uses s=floor(3r/2). Other notation from connectivity-certificate.py."""
import sympy as sy
r,k,x,y=sy.symbols("r k x y", real=True)
s=(3*r-1)/2
N=(r+3)*k+1-r*(r+1)
u=(N-2*s+1)/(s+5)
v=(N-s+1)/(s+2)
f=lambda q:(2*k-3*q+2)*q+2*k-3*q-1-N
g=lambda b:(k-b+3)*b+k-b+1-N
tests=[(2*k-3)/3-u,f(k/2),f(u),g(k/2+1),g(v)]
for rr,kk in [(20+y,3*r+1+x),*[(i,200+x) for i in range(5,20,2)]]:
    for expr in tests:
        top=sy.fraction(sy.together(expr))[0]
        pol=sy.Poly(top.subs(k,kk).subs(r,rr).expand(), x,y)
        assert min(pol.coeffs())>0 and pol.eval({x:0,y:0})>0, (rr,pol)
big,small=[],[]
for rr in range(5,20,2):
    s=3*rr//2
    for kk in range(2*s+2,200):
        n=(rr+3)*kk+1-rr*(rr+1)
        h=(kk+1)//2
        for q in range(h,(n-2*s+1)//(s+5)+1):
            if 3*q>2*kk-3 or (2*kk-3*q+2)*q+2*kk-3*q-1<=n:
                big.append((rr,kk,q))
        for b in range(h+1,min(kk-1,(n-s+1)//(s+2))+1):
            if (kk-b+3)*b+kk-b+1<=n:
                small.append((rr,kk,b))
assert not big, big
assert small==[(5,16,9),(5,16,10),(5,17,11),(5,18,12)], small
print("45 endpoint tests passed. Residuals",big,small)
