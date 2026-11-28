"""Verify explicit routes in all 72 pre-completion rows at order 15 and k=4."""
from collections import Counter
from itertools import combinations,permutations
from pathlib import Path
import json

here=Path(__file__).resolve().parent
rows=json.loads((here/'k4-order15-rows.json').read_text())
assert len(rows)==72
classes=Counter(); losses=Counter(); arms=Counter()


def segment(a,b):
    step=1 if a<b else -1
    return tuple(range(a,b+step,step))

def check(path, trueEdges=()):
    assert len(path)==len(set(path)) and len(path)>=12,(record,path)
    known=set(tuple(sorted(e)) for e in trueEdges)
    assert all((v in graph[u] or tuple(sorted((u,v))) in known) for u,v in zip(path,path[1:])),(record,path)
    losses[15-len(path)]+=1

for record in rows:
    p=record['p']; z=14
    graph=[{j for j in range(15) if q>>j&1} for q in record['lower']]
    E=set(range(p,14)); P=set(range(p)); arcs=set.union(*(graph[e]&P for e in E))
    assert all(u not in graph[u] and all(u in graph[v] for v in graph[u]) for u in range(15))
    assert all(i+1 in graph[i] for i in range(p-1))
    forced={e for e in E if len(graph[e]-{z})==3}
    assert graph[z]&E==forced
    if len(arcs)==1:
        classes['single mark']+=1
        c,=arcs; reachable=E&graph[c]; arms[max(c,p-c-1)]+=1
        assert max(c,p-c-1)<=7
        for size in range(1,len(E)+1):
            for S in combinations(sorted(E),size):
                Z=set(S)
                if not forced<=Z or (len(Z)==1 and Z==reachable):continue
                exterior=next(t for t in permutations(sorted(E)) if t[0] in reachable and t[-1] in Z
                              and all(v in graph[u] for u,v in zip(t,t[1:])))
                for j in P-{c}:
                    tip=0 if j<c else p-1
                    near=c-1 if j<c else c+1
                    arm=max([segment(j,tip),segment(j,near)],key=len)
                    check(segment(p-1-tip,c)+exterior+(z,)+arm,[(z,exterior[-1]),(z,j)])
    elif len(E)==3:
        assert p==11 and arcs=={3,7} and all((E-{e})<=graph[e] and graph[e]&P for e in E)
        if forced:
            classes['two marks, triangle with forced z-edge']+=1
        else:
            classes['two marks, triangle with no forced z-edge']+=1
            assert all((graph[e]&P)=={3,7} for e in E)
        for start in forced or E:
            tail=tuple(sorted(E-{start})); c=min(graph[tail[-1]]&P)
            check((z,start)+tail+segment(c,10 if c==3 else 0),[(z,start)])
        if not forced:
            # z avoids E. Saturation removes 3 and 7. Order 15 gives d(z)>=4.
            for e in E:
                for w,c in ((2,3),(4,3),(6,7),(8,7)):
                    assert w not in graph[e] and c in graph[e] and w in graph[c]
            for S in combinations(sorted(P-arcs),4):
                Z=set(S); special=Z&{0,4,6,10}
                if special:
                    v=min(special)
                    route=(0,1,2,3,11,12,13,7,6,5,4)
                    if v in (6,10):route=tuple(10-u if u in P else u for u in route)
                    if route[-1]==v:route=route[::-1]
                    assert route[0]==v
                    check((z,)+route,[(z,v)])
                else:
                    i=1 if {1,2}<=Z else 8
                    assert {i,i+1}<=Z
                    check(segment(0,i)+(z,)+segment(i+1,10),[(z,i),(z,i+1)])
    else:
        classes['four marks, singleton and K4']+=1
        assert p==9 and len(E)==5
        iso,=[e for e in E if not graph[e]&E]; block=tuple(sorted(E-{iso}))
        assert all(set(block)-{e}<=graph[e] and (graph[e]&P)=={4} for e in block)
        arr=(0,1,2,3,iso,7,6,5,4)
        if 7 not in graph[iso]:arr=tuple(8-v if v in P else v for v in arr)
        check(arr+block)
assert sorted(classes.values())==[1,2,24,45]
print('terminal families',dict(classes));print('one-mark maximum arm orders',dict(sorted(arms.items())))
print('concrete route checks by number of omissions',dict(sorted(losses.items())))
