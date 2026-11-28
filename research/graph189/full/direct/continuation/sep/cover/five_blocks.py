"""Integer degree bounds for the large-block cases at k=19..25, connectivity >=5."""
import argparse
from math import isqrt
from pathlib import Path

def hamilton_connected(degrees, core_size, deficit):
    order = len(degrees)
    threshold = (order + 2) // 2
    remainder = degrees[core_size:]
    if (order >= 2*deficit + 3 and 2*core_size >= order + 1
            and min(remainder, default=order) >= deficit + 2):
        return True
    return min(degrees) >= 3 and sum(value < threshold for value in degrees) <= 1

def large_cases(k, s):
    h = (k + 1) // 2
    upper = 2*k + 1 + isqrt(k*k*(k+1) + 1)
    for whole in (True, False):
        for q in range(h, upper // (s+5) + 1):
            preliminary = (s+5)*q + 2*s - 1 + (0 if whole else h-3)
            if preliminary > upper:
                continue
            for r in range(2, 2*q-k+2):
                assert 2*q-1 - (q+1) - r - 1 > 0, (k, q, r)
                min_c = 2*q + 2 + (0 if whole else h)
                if whole and preliminary+2 > upper:
                    continue
                for low_in_h in range(1 + int(r <= 2*q-k)):
                    size = q + 1 - low_in_h
                    credit = int(low_in_h or (whole and r == 2*q-k+1))
                    min_h_degree = k-q-low_in_h
                    ordinary = 2*min_h_degree >= size+1
                    low_tie = low_in_h and 2*min_h_degree == size and min_h_degree >= 3
                    route = size if ordinary or low_tie else min_h_degree+1
                    for j in range(max(1,k-q-r+1),size+1):
                        if min_c+j+(j+1)*route+2*(q-r+1+credit) > upper:
                            break
                        for p in range(max(0,k-q-r), j+1):
                            u = j-p
                            x_required = int(k-q>p)
                            if u<x_required:
                                continue
                            w = size-u
                            deficit = q+r+p-k
                            assert w>0 and deficit>=0
                            case = whole,q,r,low_in_h,j,p
                            bounds = upper,size,min_c,credit,min_h_degree,w,deficit,x_required
                            yield case,bounds

def core_lower(s, case, bounds):
    whole,q,r,low_in_h,j,p = case
    upper,size,min_c,credit,min_h_degree,w,deficit,x_required = bounds
    # The i-th best gateway has at most this many missing W-neighbors:
    # every gateway ranked below it must miss at least the same number.
    count = r+low_in_h
    guaranteed = [max(0,w-w*deficit//(count-i)) for i in range(count)]
    best = 0
    for g in range(count+1):
        if g and guaranteed[g-1]<2:
            break
        order = size+g
        degrees = ([order-1-deficit]*w + [size-1]*x_required
                   + [min_h_degree]*(j-p-x_required) + guaranteed[:g])
        if not hamilton_connected(degrees,w,deficit):
            continue
        gain = q-r+credit+int(g==0)
        direct = min_c+j+(j+1)*order+2*gain
        extras = min(4,2+gain,2*gain)
        disjoint = min_c+s+(s+1)*order+extras
        best = max(best,direct,disjoint)
    return best

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('lower',type=int)
    parser.add_argument('upper',type=int)
    parser.add_argument('--connectivity',type=int,default=5)
    opts=parser.parse_args()
    lease=Path(__file__).resolve().parents[2]
    for k in range(opts.lower,opts.upper+1):
        for case,bounds in large_cases(k,opts.connectivity):
            if not (lease/'LIVE').exists() or any((lease/x).exists() for x in ('HALT','PAUSE')):
                raise SystemExit(1)
            print(k,*map(int,case),bounds[0],core_lower(opts.connectivity,case,bounds),flush=True)
