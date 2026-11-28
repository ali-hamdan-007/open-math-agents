"""Construct explicit lower-path and upper-obstruction certificates on finite vertex sets."""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
from collections import Counter
import json
here=Path(__file__).resolve().parent
def verts(mask):
    while mask:
        b=mask&-mask;yield b.bit_length()-1;mask-=b
def change(rows,a,b,insert=True):
    r=list(rows)
    if insert:r[a]|=1<<b;r[b]|=1<<a
    else:r[a]&=~(1<<b);r[b]&=~(1<<a)
    return tuple(r)
def paths(rows,allow,want):
    @lru_cache(None)
    def extend(v,used):
        if used.bit_count()==want:return (v,)
        for w in verts(rows[v]&allow&~used):
            end=extend(w,used|1<<w)
            if end:return (v,)+end
        return ()
    for x in verts(allow):
        path=extend(x,1<<x)
        if path:return list(path)
    return []
def make(r):
    n,k,p=r['n'],r['k'],r['p'];z=n-1;allv=(1<<n)-1
    full=n-(k+1)//2-1
    lo=tuple(r['lower'])
    l0=lo
    opt=[(a,b) for a,b in combinations(range(n),2) if (b<p or b==z) and not (lo[a]>>b)&1]
    up=lo
    for a,b in opt:up=change(up,a,b)
    u0=up
    req=[k]*z+[2]
    @lru_cache(None)
    def long(g):
        for scope,allowed,target in [('G',allv,full),('H',allv^(1<<z),p+1)]:
            seq=paths(g,allowed,target)
            if seq:return {'scope':scope,'vertices':seq}
    steps=[]
    while True:
        route=long(lo)
        if route:
            end=dict(kind='path',**route);break
        blocked={}
        for a,b in opt:
            if ((up[a]&~lo[a])>>b)&1:
                route=long(change(lo,a,b))
                if route:blocked[a,b]=route
        final=up
        for a,b in blocked:final=change(final,a,b,False)
        if not steps:
            choices=[]
            def proposal(edges,leaf):
                edges=sorted(set(edges))
                if all(e in blocked for e in edges):
                    choices.append((len(edges),edges,leaf))
            for v in range(n):
                if final[v].bit_count()<req[v]:
                    num=max(0,up[v].bit_count()-req[v]+1)
                    ed=[e for e in blocked if v in e][:num]
                    possible=set(verts(up[v]))-{b if a==v else a for a,b in ed}
                    proposal(ed,dict(kind='degree',v=v,available=sorted(possible),required=req[v]))
                candidates=[]
                for y in range(n):
                    common=lo[v]&lo[y]
                    if v!=y and common and not (final[v]>>y)&1:
                        candidates.append((bool(up[v]>>y&1),y,next(verts(common))))
                if len(candidates)>k:
                    chosen=sorted(candidates)[:k+1]
                    proposal([tuple(sorted((v,y))) for miss,y,m in chosen if miss],
                             dict(kind='even',v=v,pairs=[[y,m] for _,y,m in chosen]))
                rest=allv^(1<<v);pieces=[]
                while rest:
                    cc=rest&-rest
                    while True:
                        grow=cc
                        for u in verts(cc):grow|=final[u]&rest
                        if grow==cc:break
                        cc=grow
                    pieces.append(cc);rest^=cc
                if len(pieces)>1:
                    # Either part can be used as the cut witness.
                    for subset in range(1,1<<len(pieces)-1):
                        lhs=sum(pieces[i] for i in verts(subset));rhs=(allv^(1<<v))^lhs
                        ed=[tuple(sorted((a,b))) for a in verts(lhs) for b in verts(rhs&up[a])]
                        proposal(ed,dict(kind='cut',v=v,left=list(verts(lhs)),right=list(verts(rhs))))
            if choices:
                _,ed,end=min(choices,key=lambda option:option[0])
                steps.extend(dict(kind='forbid',a=a,b=b,**blocked[a,b]) for a,b in ed)
                break
        deficient=[v for v in range(n) if final[v].bit_count()<req[v]]
        if deficient:
            v=min(deficient,key=lambda v:up[v].bit_count()-req[v])
            for (a,b),route in blocked.items():
                if v in (a,b) and up[v].bit_count()>=req[v]:
                    steps.append(dict(kind='forbid',a=a,b=b,**route))
                    up=change(up,a,b,False)
            end=dict(kind='degree',v=v,available=list(verts(up[v])),required=req[v]);break
        for (a,b),route in blocked.items():
            steps.append(dict(kind='forbid',a=a,b=b,**route))
        up=final
        end=None
        for cut in range(n):
            available=allv^(1<<cut)
            reached=available&-available
            while True:
                grow=reached
                for w in verts(reached):grow|=up[w]&available
                if grow==reached:break
                reached=grow
            if reached!=available:
                end=dict(kind='cut',v=cut,left=list(verts(reached)),right=list(verts(available^reached)));break
        if end:break
        for v in range(n):
            wit=[]
            for y in range(n):
                common=lo[v]&lo[y]
                if v!=y and not (up[v]>>y)&1 and common:
                    wit.append([y,next(verts(common))])
            if len(wit)>k:
                end=dict(kind='even',v=v,pairs=wit[:k+1]);break
        if end:break
        forced=[]
        for v in range(n):
            if up[v].bit_count()==req[v]:
                for w in verts(up[v]&~lo[v]):
                    forced.append(dict(kind='force',a=v,b=w,available=list(verts(up[v]))))
                    lo=change(lo,v,w)
        assert forced,(r['id'],'unresolved interval')
        steps.extend(forced)
    if all(t['kind']=='forbid' for t in steps):
        if end['kind']=='cut':
            left=set(end['left']);right=set(end['right'])
            steps=[t for t in steps if (t['a'] in left and t['b'] in right) or (t['b'] in left and t['a'] in right)]
        elif end['kind']=='even':
            needs={tuple(sorted((end['v'],y))) for y,middle in end['pairs']}
            steps=[t for t in steps if (t['a'],t['b']) in needs]
        elif end['kind']=='path':
            steps=[]
    return dict(id=r['id'],k=k,n=n,p=p,ext=r['ext'],contacts=r['contacts'],lower=l0,upper=u0,steps=steps,end=end)
def main():
    for k in range(3,7):
        pats=json.loads((here/f'patterns-{k}.json').read_text())
        rows=[make(p) for p in pats]
        (here/f'traces-{k}.json').write_text(json.dumps(rows,indent=1)+'\n')
        print(k,Counter(t['end']['kind'] for t in rows),Counter(step['kind'] for row in rows for step in row['steps']),flush=True)
if __name__=='__main__':main()
