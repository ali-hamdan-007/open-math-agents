"""Independent integer replay of the original exterior proof for two order-envelope tables."""
from math import isqrt
from pathlib import Path
import sys

def load_rows(source):
    result = {}
    for line in Path(source).read_text().splitlines():
        words = line.split()
        if not words or not words[0].isdecimal():
            continue
        s, k, lower, upper = map(int, words[:4])
        assert (s,k) not in result
        result[s,k] = (lower,upper)
    return result

def large_survives(k,s,upper):
    h=(k+1)//2
    for end in (False,True):
        for q in range(h,upper//(s+5)+1):
            cycle=(s+5)*q+2*s-1 + (h-3 if end else 0)
            if cycle>upper: continue
            assert q<k
            for r in range(2,2*q-k+2):
                assert q-r-3>0
                if not end and cycle+2>upper: continue
                m=2*q+2+(h if end else 0)
                for low in (0,1):
                    if low and r>2*q-k: continue
                    H=q+1-low
                    D=k-q-low
                    gain=int(low or (not end and r==2*q-k+1))
                    dist_route=D+1
                    if 2*D>=H+1 or (low and 2*D==H and D>=3):
                        dist_route=H
                    for j in range(max(1,k-q-r+1),H+1):
                        if m+j+(j+1)*dist_route+2*(q-r+1+gain)>upper:continue
                        assert j<H
                        for u in range(j+1):
                            p=j-u
                            a=q+r+p-k
                            if a<0:continue
                            covered_x=int(p<k-q)
                            if covered_x>u:continue
                            W=H-u
                            t=r+low
                            ok=False
                            for g in range(t+1):
                                N=H+g
                                extensions=[max(0,W-W*a//(t-i)) for i in range(g)]
                                if extensions and min(extensions)<2:continue
                                others=[H-1]*covered_x + [D]*(u-covered_x)+extensions
                                ds=[N-1-a]*W+others
                                hc=(min(ds)>=3 and sum(2*value<N+1 for value in ds)<=1)
                                hc |= (N>=2*a+3 and 2*W>=N+1 and all(v>=a+2 for v in others))
                                if not hc:continue
                                bonus=q-r+gain+(g==0)
                                gap=m+j+(j+1)*N+2*bonus
                                men=m+s+(s+1)*N+min(4,2+bonus,2*bonus)
                                if max(gap,men)>upper:
                                    ok=True
                                    break
                            if not ok:
                                return end,q,r,low,j,p
    return None

def replay(s,k,lo,hi):
    assert lo<=hi and s>=5 and k>5*s
    h=(k+1)//2
    for j in range(s,(k-1)//3+1):
        m=max(h+2,k-j//2+2)
        assert (j+2)*m+j-1>hi,('near',s,k,j,m)
    for b in range(h+1,hi//(s+1)+1):
        j=max(s-1,k-b+1)
        assert (j+2)*b+3*h-1>hi,('small',s,k,b,j)
    res=large_survives(k,s,hi)
    assert res is None,('large',s,k,lo,hi,res)

if __name__=='__main__':
    first, second=map(load_rows,sys.argv[1:3])
    counts={}
    for key in sorted(first.keys() & second.keys()):
        s,k=key
        lo=max(first[key][0],second[key][0]); hi=min(first[key][1],second[key][1])
        if lo>hi:continue
        replay(s,k,lo,hi)
        counts.setdefault(s,[]).append(k)
    for s,ks in counts.items():print(s,len(ks),min(ks),max(ks))
    print('total',sum(map(len,counts.values())))
