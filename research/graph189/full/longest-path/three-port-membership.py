"""Membership/boundary enumeration in the delta-four three-port residual."""
from itertools import combinations_with_replacement, product
from collections import Counter
MASKS = tuple(range(1,8))
BITS = (1,2,4)

def port_patterns():
    for es in range(8):
        adj=[0,0,0]
        for bit,(i,j) in enumerate(((0,1),(0,2),(1,2))):
            if es>>bit & 1:
                adj[i]|=1<<j;adj[j]|=1<<i
        yield adj

def check(k):
    counts=Counter()
    sols=[]
    for r in range(2*k-2,(3*k+3)//2+1):
        for M in combinations_with_replacement(MASKS,r):
            private=sum(x.bit_count()==1 for x in M)
            if private>6:continue
            sizes=[sum(bool(x & b) for x in M) for b in BITS]
            # An empty S_i would leave two sets of size <=k-1 covering r>=2k-2;
            # equality forces disjointness and r>=8 privates, more than six.
            if max(sizes)>k-1:continue
            counts['memberships']+=1
            for A in port_patterns():
                # Some other ports are at distance two from port i.
                capacities=[]
                for i,b in enumerate(BITS):
                    used=sum(i!=j and not (A[i]&a) and
                             (bool(A[i]&A[j]) or any(x&b and x&a for x in M))
                             for j,a in enumerate(BITS))
                    capacities.append(2-used)
                # If p-q is a port edge then q's remotes outside S_p are p boundary.
                options=[]
                for x in M:
                    mandatory=0
                    for i,b in enumerate(BITS):
                        if not x&b and x&A[i]:mandatory|=b
                    options.append([v for v in range(8) if not(v&x) and
                                    (v&mandatory)==mandatory and (x.bit_count()>1 or v)])
                def visit(i,B,left):
                    if i==r:
                        counts['boundary configurations']+=1
                        for u,x in enumerate(M):
                            degree=x.bit_count()+sum(
                                v!=u and not (y & ~(x|B[u])) and not (x & ~(y|B[v]))
                                for v,y in enumerate(M))
                            if degree<k:return
                        counts['degree-feasible configurations']+=1
                        if len(sols)<100:sols.append((r,M,A,B))
                        return
                    for v in options[i]:
                        if i and M[i]==M[i-1] and v<B[-1]:continue
                        if any(v&b and left[j]==0 for j,b in enumerate(BITS)):continue
                        visit(i+1,B+(v,),tuple(l-int(bool(v&b)) for l,b in zip(left,BITS)))
                visit(0,(),tuple(capacities))
    return counts,sols
if __name__=='__main__':
    import sys
    for k in map(int,sys.argv[1:] or [5,6,7]):
        c,s=check(k)
        print(k,dict(c),flush=True)
        assert not s, ('Unexpected degree-feasible configuration',k,s[0] if s else None)
