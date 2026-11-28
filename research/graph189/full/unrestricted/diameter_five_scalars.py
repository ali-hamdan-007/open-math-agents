"""Necessary diameter-five inequalities in the range n > 3s+2."""
from collections import Counter
from itertools import product
import sys

def records(h):
    cmax = (h+1)**2//4-1
    lmax = cmax-h-2
    amax = 4*max(h,lmax)
    for l in range(2,lmax+1):
        for g in range(cmax-h-l-1):
            for i in range(1,amax-h-g):
                for j in range(amax-i-h-g):
                    a=i+h+1+j+g
                    if a>4*max(h,l): continue
                    s=a+l
                    f=s-h
                    d=h+1+j
                    for m in range(1,min(i,h-1)+1):
                        r=j+g+m+2
                        c_upper=min(cmax,(m+1)*(h-m)-1,a*(h-m)//r)
                        for c in range(h+l+g+2,c_upper+1):
                            for L in range(h-m+1):
                                for H in range(l+1):
                                    if not (L or H) or L+H>c or (L and H==l): continue
                                    if c < h+l+g+2+i-m: continue
                                    if L and (i+g+1>l or c>(m+1)*(h-m)-m*L): continue
                                    if H and r>h: continue
                                    if L*l<f and H*h<a: continue
                                    visible=(c-L-H)*r+L*a+max(H*r,a if L*l<f else 0)
                                    omitted_b=max(a*m,(i+H)*(a-h) if L*l<f else ((a-h) if H else 0))
                                    if visible+omitted_b>a*h:continue
                                    if not H:
                                        if not any(f*(t-l)<=t*l for t in range(max(1,a-2*l,h+1),d+1)):continue
                                    yield (a,s,i,j,g,m,c,L,H)

if __name__=="__main__":
    for h in map(int,sys.argv[1:]):
        vals=list(records(h))
        print(h,len(vals),Counter(('mixed' if L and H else 'left' if L else 'right') for *_,L,H in vals))
        print(vals)
