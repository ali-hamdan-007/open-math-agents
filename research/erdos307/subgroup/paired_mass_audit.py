from math import isqrt, lcm

LIMIT = 12000000
SCALE = 10**10
is_prime = bytearray(b"\1") * (LIMIT + 1)
for p in range(2, isqrt(LIMIT) + 1):
    if is_prime[p]:
        is_prime[p*p:LIMIT+1:p] = bytes((LIMIT-p*p)//p + 1)
primes = [p for p in range(3, LIMIT + 1, 2) if is_prime[p]]

import sys
ell=int(sys.argv[1]) if len(sys.argv)>1 else 43
budget=ell-2
reserved=6
prefixes=[[0] for _ in range(ell)]
for p in primes:
    row=prefixes[p%ell]
    row.append(row[-1]+(SCALE+p-1)//p)
best=[[0]*(reserved+1) for _ in range(budget+1)]
for r in range(1,(ell+1)//2):
    d=lcm(2,next(k for k in range(1,ell) if pow(r,2*k,ell)==1))
    left,right=prefixes[r],prefixes[-r]
    pair=[]
    for q in range(budget+1):
        row=[]
        for c in range(reserved+1):
            big=d*(q+2)-2
            row.append(max(max(left[q+f]+right[big+c-f],left[big+f]+right[q+c-f],
                               max(left[m+f]+right[d+2*q-m+c-f] for m in range(q+1,d+q)))
                           for f in range(c+1)))
        pair.append(row)
    best=[[max(best[q-u][c-f]+pair[u][f] for u in range(q+1) for f in range(c+1)) for c in range(reserved+1)] for q in range(budget+1)]
print(best[budget])
