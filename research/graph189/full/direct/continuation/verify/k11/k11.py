"""Exact support/count relaxation for the terminal four-anchor cases at second degree eleven."""
import argparse
import ctypes
import itertools
from pathlib import Path

S=range(4)
pairs=list(itertools.combinations(S,2))

def plus(terms):
    terms=list(terms)
    return '0' if not terms else terms[0] if len(terms)==1 else '(+ '+' '.join(terms)+')'

def or_(terms):
    terms=list(terms)
    return 'false' if not terms else terms[0] if len(terms)==1 else '(or '+' '.join(terms)+')'

def gen(edges, low, order, size, timeout=10000, model=False, override_b=None):
    delta=11 if low=="none" else max(8,order-48)
    bsize=order-4-size if override_b is None else override_b
    d=[[0]*4 for _ in S]
    for e,(i,j) in zip(edges,pairs):
        d[i][j]=d[j][i]=int(e)
    specs=[]
    for side in ('A','B'):
        for islow in ([False,True] if side==low else [False]):
            for v in itertools.product(*(range(1,6 if islow or low==str(i) else 5) for i in S)):
                if any(abs(v[i]-v[j])>d[i][j] or v[i]+v[j]<d[i][j] for i,j in pairs):
                    continue
                if side=='A':
                    if size==8:
                        if max(v)>2 or (not islow and v!=(1,1,1,1)):continue
                        if islow and not (delta-7<=v.count(1)<=3):continue
                    else:
                        if not islow and (v.count(1)<3 or max(v)>2):continue
                        if islow and v.count(1)<delta-8:continue
                    if any(v[j]==1 and sum(d[j][i]<v[i] for i in S)>=2 for j in S):continue
                if side=='B' and min(v)>(4 if islow else 3):continue
                specs.append((side,islow,v))
    xs=['c'+str(i) for i in range(len(specs))]
    on=['p'+str(i) for i in range(len(specs))]
    q=['(set-logic QF_LRA)','(set-option :timeout '+str(timeout)+')']
    def ass(term):q.append('(assert '+term+')')
    def gate(t,term):ass('(=> '+on[t]+' '+term+')')
    for t,(s,l,v) in enumerate(specs):
        q.extend(['(declare-const '+xs[t]+' Real)','(declare-const '+on[t]+' Bool)'])
        ass('(ite '+on[t]+' '+(('(= ' if l else '(>= ')+xs[t]+' 1)')+' (= '+xs[t]+' 0))')
    if low in ('A','B'):ass('(= '+plus(xs[t] for t,(_,l,_) in enumerate(specs) if l)+' 1)')
    for side,num in [('A',size),('B',bsize)]:
        ass('(= '+plus(xs[t] for t,(s,l,v) in enumerate(specs) if s==side)+' '+str(num)+')')
    for sz in range(1,5):
        for T in itertools.combinations(S,sz):
            ass('(>= '+plus(xs[t] for t,(s,l,v) in enumerate(specs) if s=='B' and any(v[i]==1 for i in T))+' '+str(2*sz if size==9 else max(sz,2*sz-2))+')')
    for i in S:
        ass(or_(on[t] for t,(s,l,v) in enumerate(specs) if s=='A' and v[i]==1))
        ds_count=sum(d[i][j]==1 for j in S)
        deg=plus(xs[t] for t,(_,_,v) in enumerate(specs) if v[i]==1)
        if low==str(i):
            ass('(>= '+deg+' '+str(delta-ds_count)+')')
            ass('(<= '+deg+' '+str(10-ds_count)+')')
        else:ass('(>= '+deg+' '+str(11-ds_count)+')')
        ass('(<= '+plus(xs[t] for t,(_,_,v) in enumerate(specs) if v[i]%2==0)+' '+str(11-sum(j!=i and d[i][j]%2==0 for j in S))+')')
    for t,(side,l,v) in enumerate(specs):
        forced=[];outer=[]; layer4=[]; potential=[];pred=[[] for i in S]
        for u,(ss,ll,w) in enumerate(specs):
            lb=max(abs(a-b) for a,b in zip(v,w))
            via=min(a+b for a,b in zip(v,w))
            ub=min(via,5 if l or ll else 4)
            if side!=ss:
                if via>ub and t<u:gate(t,'(not '+on[u]+')')
                if via in (2,4): forced.append(xs[u]);outer.append(xs[u])
                if via==4:layer4.append(xs[u])
                continue
            if lb==ub and lb in (2,4):
                forced.append(xs[u])
                if lb==4:outer.append(xs[u])
            ok=lb<=1
            if side=='A' and ok:
                if max(sum(a>b for a,b in zip(v,w)),sum(a<b for a,b in zip(v,w)))>=2:ok=False
            if ok:
                potential.append(xs[u])
                for i in S:
                    if w[i]+1==v[i]:pred[i].append(on[u])
        gate(t,'(<= '+plus(forced)+' '+str(11-sum(a%2==0 for a in v))+')')
        gate(t,'(<= '+plus(outer)+' '+str(11-4+v.count(1)-v.count(4))+')')
        gate(t,'(<= '+plus(layer4)+' 7)')
        gate(t,'(>= '+plus(potential)+' '+str((delta if l else 11)+1-v.count(1))+')')
        for i in S:
            if v[i]>1 and not any(v[j]==1 and d[j][i]+1==v[i] for j in S):
                gate(t,or_(pred[i]))
    q.append('(check-sat)')
    if model:q.append('(get-value ('+' '.join(xs)+'))')
    return '\n'.join(q),specs

def run(formula):
    z=ctypes.CDLL('libz3.so.4')
    ptr=ctypes.c_void_p
    z.Z3_mk_config.restype=ptr
    z.Z3_mk_context.argtypes=[ptr];z.Z3_mk_context.restype=ptr
    z.Z3_eval_smtlib2_string.argtypes=[ptr,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    return z.Z3_eval_smtlib2_string(z.Z3_mk_context(z.Z3_mk_config()),formula.encode()).decode().strip()

def cases():
    perms=list(itertools.permutations(S))
    for size in (8,9):
        for ed in itertools.product('12' if size==8 else '123',repeat=6):
            ds=dict(zip(pairs,ed))
            def dij(i,j):return 0 if i==j else int(ds[tuple(sorted((i,j)))])
            if any(dij(i,j)>dij(i,x)+dij(x,j) for i,j,x in itertools.permutations(S,3)):continue
            def permute(pm):return tuple(ds[tuple(sorted((pm[i],pm[j])))] for i,j in pairs)
            if ed!=min(permute(pm) for pm in perms):continue
            autos=[pm for pm in perms if permute(pm)==ed]
            for order in (range(56,60) if size==8 else range(58,60)):
                for low in (('none','A','B','0','1','2','3') if order<59 else ('none',)):
                    if low.isdigit() and min(p[int(low)] for p in autos)!=int(low):continue
                    yield ''.join(ed),low,order,size
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('edges');p.add_argument('low');p.add_argument('order',type=int);p.add_argument('size',type=int);p.add_argument('--timeout',type=int,default=10000)
    a=p.parse_args();f,_=gen(a.edges,a.low,a.order,a.size,a.timeout);print(run(f),flush=True)
