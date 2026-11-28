"""Exact integer verification of the final exterior order intervals."""
from pathlib import Path
from sys import argv

def read(path):
    rows={}
    for line in path.read_text().splitlines():
        fields=line.split()
        if not fields or not fields[0].isdigit():continue
        s,k,lo,hi=map(int,fields[:4])
        assert (s,k) not in rows and lo<=hi
        rows[s,k]=(lo,hi)
    return rows

def core_works(k,s,upper,min_c,q,r,l,credit,j,p):
    size=q+1-l
    minimum=k-q-l
    u=j-p
    w=size-u
    special=int(k-q>p)
    a=q+r+p-k
    assert w>0 and a>=0 and u>=special
    count=r+l
    for g in range(count+1):
        n=size+g
        gain=q-r+credit+int(g==0)
        direct=min_c+j+(j+1)*n+2*gain
        extra=min(4,2+gain,2*gain)
        disjoint=min_c+s+(s+1)*n+extra
        if max(direct,disjoint)<=upper:continue
        assert n>=s
        # Guaranteed W degree of the g-th best addition.
        worst=w-(w*a)//(count-g+1) if g else n
        if g and worst<2:break
        other_degrees=[worst]
        if special:other_degrees.append(size-1)
        if u>special:other_degrees.append(minimum)
        min_other=min(other_degrees)
        if n>=2*a+3 and 2*w>=n+1 and min_other>=a+2:
            return True
        if min(n-1-a,min_other)<3:continue
        threshold=(n+2)//2
        bad=w*int(n-1-a<threshold)+special*int(size-1<threshold)+(u-special)*int(minimum<threshold)
        if g and worst<threshold:
            bad+=1
            if g>=2 and w-(w*a)//(count-g+2)<threshold:bad+=1
        if bad<=1:return True
    return False

def check(s,k,upper):
    h=(k+1)//2
    # The admissible integer contact matchings satisfy s<=j and 3j<k.
    assert all((j+2)*(k-j//2+2)+j-1>upper for j in range(s,(k+2)//3))
    assert 3*h-1+min((h+1)*(k-h+2),(s+1)*(k-s+2))>upper
    visited=0
    for whole in (True, False):
        for q in range(h,upper//(s+5)+1):
            prelim=(s+5)*q+2*s-1+(0 if whole else h-3)
            if prelim>upper:continue
            for r in range(2,2*q-k+2):
                assert q-r-3>0 and k>q
                min_c=2*q+2+(0 if whole else h)
                if whole and prelim+2>upper:continue
                for l in range(1+int(r<=2*q-k)):
                    size=q+1-l
                    credit=int(l or (whole and r==2*q-k+1))
                    minimum=k-q-l
                    ordinary=2*minimum>=size+1
                    low_tie=l and 2*minimum==size and minimum>=3
                    route=size if ordinary or low_tie else minimum+1
                    for j in range(max(1,k-q-r+1),size+1):
                        if min_c+j+(j+1)*route+2*(q-r+1+credit)>upper:break
                        for p in range(max(0,k-q-r),j+1):
                            if k-q>p and j==p:continue
                            visited+=1
                            assert core_works(k,s,upper,min_c,q,r,l,credit,j,p),(s,k,whole,q,r,l,j,p)
    return visited

if __name__=='__main__':
    here=Path(__file__).resolve().parent
    lease=here.parents[2]
    double='--double' in argv
    if double:
        rows=read(here/'double-input.tsv')
    else:
        left=read(here/'pointwise-input.tsv')
        right=read(here/'column-input.tsv')
        rows={}
        for key in left.keys() & right.keys():
            lo=max(left[key][0],right[key][0]);hi=min(left[key][1],right[key][1])
            if lo<=hi:rows[key]=(lo,hi)
    assert len(rows)==(64 if double else 82)
    print('s\tk\tnmin\tnmax\tlarge_block_tuples')
    for (s,k),(lo,hi) in sorted(rows.items()):
        if not (lease/'LIVE').exists() or any((lease/x).exists() for x in ('HALT','PAUSE')):
            raise SystemExit(1)
        if '--s' in argv and s!=int(argv[argv.index('--s')+1]):continue
        print(s,k,lo,hi,check(s,k,hi),sep='\t',flush=True)
