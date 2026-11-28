"""Exact-real feasibility of necessary counts; uses system Z3 via its C API."""
import argparse, ctypes, itertools, json
from pathlib import Path
F=range(3)
def add(xs):
    xs=list(xs)
    return '0' if not xs else xs[0] if len(xs)==1 else '(+ '+' '.join(xs)+')'
def dis(xs):
    xs=list(xs)
    return 'false' if not xs else xs[0] if len(xs)==1 else '(or '+' '.join(xs)+')'
def app(s):
    return '('+s+')'
def build(ds,low,absent,big,limit,absent_a=0):
    dv={(0,1):ds[0],(0,2):ds[1],(1,2):ds[2]}
    D=[[dv[tuple(sorted((i,j)))] if i!=j else 0 for j in F] for i in F]
    sm=['(set-option :timeout '+str(limit)+')','(set-logic QF_LRA)','(declare-const k Real)','(assert (>= k 16))']
    def ass(expr):sm.append('(assert '+expr+')')
    def raw(kflag,sideflag):
        for v in itertools.product(*[range(1,6 if kflag or low==str(i) else 5) for i in F]):
            if any(abs(v[i]-v[j])>D[i][j] or v[i]+v[j]<D[i][j] for i,j in itertools.combinations(F,2)):continue
            if min(v)>(3 if kflag else 2):continue
            if not kflag and min(v)==2 and v.count(2)==1 and v[absent if sideflag=='B' else absent_a]==2:continue
            yield v
    types=[(side,l,v) for side in ('A','B') for l in ([0,1] if side==low else [0]) for v in raw(l,side)]
    if any(D[i][j]>(5 if low in (str(i),str(j)) else 4) or D[i][j]>D[i][t]+D[t][j] for i,j,t in itertools.permutations(F)):ass('false')
    n=len(types); xs=['c'+str(i) for i in range(n)]; fs=['p'+str(i) for i in range(n)]
    for t,(side,l,v) in enumerate(types):
        sm.extend(['(declare-const '+xs[t]+' Real)','(declare-const '+fs[t]+' Bool)'])
        ass('(ite '+fs[t]+' '+('(= '+xs[t]+' 1)' if l else '(>= '+xs[t]+' 1)')+' (= '+xs[t]+' 0))')
    if low in ('A','B'):ass('(= '+add(xs[i] for i,t in enumerate(types) if t[1])+' 1)')
    ass('(>= '+add(xs)+' (- (* 5 k) 5))')
    for side in ('A','B'):
        for j in F:ass(dis(fs[i] for i,(s,l,v) in enumerate(types) if s==side and v[j]==1))
        ass(dis(fs[i] for i,(s,l,v) in enumerate(types) if s==side and min(v)>=2))
    def gated(t,e):ass('(=> '+fs[t]+' '+e+')')
    for j in F:
        anchor_degree=add(xs[t] for t,(_,l,v) in enumerate(types) if v[j]==1)
        in_s=sum(D[i][j]==1 for i in F)
        if low!=str(j):ass('(>= '+anchor_degree+' (- k '+str(in_s)+'))')
        else:ass('(>= '+anchor_degree+' '+str(3-in_s)+')')
        for i in F:
            if i==j or D[i][j]<=1 or any(D[j][l]==1 and D[l][i]+1==D[j][i] for l in F):continue
            ass(dis(fs[t] for t,(_,l,v) in enumerate(types) if v[j]==1 and v[i]+1==D[j][i]))
        used=sum(D[j][i]%2==0 for i in F if i!=j)
        ass('(<= '+add(xs[t] for t,(_,l,v) in enumerate(types) if v[j]%2==0)+' (- k '+str(used)+'))')
    asize=add(xs[u] for u,(ss,ll,ww) in enumerate(types) if ss=='A')
    for t,(s,l,v) in enumerate(types):
        forced=[]; fourth=[]; boundary=[]; neighbors=[]; preds=[[] for i in F]; no1=[]
        for u,(s2,l2,w) in enumerate(types):
            via=min(a+b for a,b in zip(v,w)); lb=max(abs(a-b) for a,b in zip(v,w)); cap=5 if l or l2 else 4
            if s!=s2:
                if via>cap:
                    if t<u:gated(t,'(not '+fs[u]+')')
                if via in (2,4):forced.append(xs[u]);boundary.append(xs[u])
                if via==4:fourth.append(xs[u])
            else:
                if lb==min(via,cap) and lb in (2,4):forced.append(xs[u])
                if lb==min(via,cap)==4:boundary.append(xs[u])
                legal=lb<=1
                if big and s=='A' and (sum(b<a for a,b in zip(v,w))>=2 or sum(b>a for a,b in zip(v,w))>=2):legal=False
                if big and s=='A' and u>t and not l and not l2 and max(sum(max(0,a-b) for a,b in zip(v,w)),sum(max(0,b-a) for a,b in zip(v,w)))>=3:
                    ass('(=> (and '+fs[t]+' '+fs[u]+') (>= '+asize+' (+ (* 2 k) '+str(2-v.count(1)-w.count(1))+')))')
                if legal:
                    neighbors.append(xs[u])
                    for j in F:
                        if w[j]==v[j]-1:preds[j].append(fs[u])
        e0=sum(a%2==0 for a in v)
        gated(t,'(<= '+add(forced)+' (- k '+str(e0)+'))')
        gated(t,'(<= '+add(fourth)+' (- k 3))')
        gated(t,'(<= '+add(boundary)+' (- k '+str(3-v.count(1)+v.count(4))+'))')
        gated(t,'(>= '+add(neighbors)+' '+('(- k '+str(v.count(1)-1)+')' if not l else str(4-v.count(1)))+')')
        for j in F:
            if big and s=='A' and v[j]==1 and sum(D[j][i]<v[i] for i in F)>=2:gated(t,'false')
            if v[j]>1 and not any(v[i]==1 and D[i][j]==v[j]-1 for i in F):
                gated(t,dis(preds[j]))
    bsize=add(xs[i] for i,(s,l,v) in enumerate(types) if s=='B')
    if big:ass('(> '+bsize+' (* 3 k))')
    else:
        ass('(<= '+bsize+' (* 3 k))')
        ass('(<= '+asize+' (* 3 k))')
    sm.append('(check-sat)')
    return '\n'.join(sm),len(types)
def run_smt(s):
    lib=ctypes.CDLL('libz3.so.4'); P=ctypes.c_void_p
    lib.Z3_mk_config.restype=P; lib.Z3_mk_context.argtypes=[P]; lib.Z3_mk_context.restype=P
    lib.Z3_eval_smtlib2_string.argtypes=[P,ctypes.c_char_p]; lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    ctxt=lib.Z3_mk_context(lib.Z3_mk_config()); return lib.Z3_eval_smtlib2_string(ctxt,s.encode()).decode().strip()
if __name__=='__main__':
    arg=argparse.ArgumentParser();arg.add_argument('ds');arg.add_argument('low');arg.add_argument('absent',type=int);arg.add_argument('big',type=int);arg.add_argument('timeout',type=int);arg.add_argument('absent_a',type=int,default=0,nargs='?');args=arg.parse_args()
    q,n=build(tuple(map(int,args.ds)),args.low,args.absent,args.big,args.timeout,args.absent_a)
    print(json.dumps([args.ds,args.low,args.absent,args.big,args.absent_a,n,run_smt(q)]),flush=True)
