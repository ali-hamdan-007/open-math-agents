from math import isqrt
from sys import argv

limit=int(argv[1]) if len(argv)>1 else 4000
max_p=isqrt(limit**3)
sieve=bytearray(b'\x01')*(max_p+1)
sieve[0:2]=b'\x00\x00'
for i in range(2,isqrt(max_p)+1):
    if sieve[i]:
        sieve[i*i::i]=b'\x00'*((max_p-i*i)//i+1)
ps=[p for p in range(3,max_p+1,4) if sieve[p] and p%5 in (2,3)]
coeff=[1,2,-1,-2,1,-13,-32,-29,2,29,72,234,438,492,432,216,72]
total_pairs=0
root_pairs=0
pass_pairs=0
def roots(p,q,lo,hi):
    lp=(p*p+p+1)*(q+1)+2*p**3
    mp=2*p**3*(p+q-1)+lp-2
    zp=2*(p**4*q+12)
    def f(x):return ((2*x-lp)*x+mp)*x-zp
    def df(x):return (6*x+6-2*lp)*x+2-lp+mp
    assert 12*hi+6 < 2*lp
    left,right=lo,hi
    while left<right:
        mid=(left+right)//2
        if df(mid)>0:left=mid+1
        else:right=mid
    peak=left
    for l,r,sgn in ((lo,peak,1),(peak+1,hi,-1)):
        if l>r or sgn*f(l)>0 or sgn*f(r)<0:continue
        while l<r:
            x=(l+r)//2
            if sgn*f(x)<0:l=x+1
            else:r=x
        if f(l)==0:
            yield l
for q in range(27,limit,40):
    if not sieve[q]:continue
    for p in ps:
        if p*p>=q**3:break
        if p<=2*q or p%3==q%3:continue
        strongest=q%3==2 or p%5==3
        if q>=4000 and (11 if strongest else 7)*p*p>=q**3:continue
        total_pairs+=1
        for x in roots(p,q,q+(6 if strongest else 4),p-1):
            root_pairs+=1
            T=((p*p+p+1)*x-(2*p**3+p*p+p+1))*x+2*p**4
            pol=0
            for c in coeff: pol=pol*p+c
            print('integral root', (p,q,x), 'prime',sieve[x], 'T positive', T>0, 'T divides', (2*pol)%T==0, flush=True)
            if sieve[x] and (p**4*q+12)%x==0 and T>0 and (2*pol)%T==0:
                print('RESIDUAL SOLUTION', (p,q,x),flush=True)
                pass_pairs+=1
print('bounded candidates:',total_pairs,'integral roots:',root_pairs,'residual solutions:',pass_pairs)
