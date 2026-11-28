"""Finite order comparisons for connectivity at least one fifth of second degree."""
from math import isqrt
from pathlib import Path
from five_blocks import large_cases,core_lower

lease=Path(__file__).resolve().parents[2]
for k in range(26,100):
    if not (lease/'LIVE').exists() or any((lease/x).exists() for x in ('HALT','PAUSE')):
        raise SystemExit(1)
    s=(k+4)//5
    h=(k+1)//2
    upper=2*k+1+isqrt(k*k*(k+1)+1)
    for j in range(s,(k+2)//3):
        m=k-j//2+2
        assert (j+2)*m+j-1>upper, (k,j,m)
    for b in range(h+1,upper//(s+1)+1):
        for j in range(max(s-1,k-b+1),upper//b):
            if (j+2)*b+3*h-1<=upper:
                assert (k,b,j)==(30,26,5)
    margins=[core_lower(s,c,bd)-upper for c,bd in large_cases(k,s)]
    assert not margins or min(margins)>0
    print(k,s,upper,len(margins),min(margins) if margins else 0)
