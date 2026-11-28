"""Standalone independent orbit/control checks, with optional fresh replay."""
from pathlib import Path
from itertools import combinations, product, permutations
from collections import Counter,deque
from concurrent.futures import ThreadPoolExecutor
import argparse, subprocess, json, sys
from clique4 import gen,run
at=Path(__file__).resolve().parent
pairs=list(combinations(range(4),2))
def orbit(edges,location,n):
    table=dict(zip(pairs,edges))
    return min((''.join(table[tuple(sorted((pm[i],pm[j])))] for i,j in pairs),
               str(pm.index(int(location))) if location in ('0','1','2','3') else location,n)
              for pm in permutations(range(4)))
def verify():
    archive={}
    for f in ['four-first.jsonl','four-retry.jsonl']:
        for line in (at/f).read_text().splitlines():
            *r,status=json.loads(line);archive[tuple(r)]=status
    expected=set();total=0
    for vals in product('12',repeat=6):
        for n,loc in [(50,z) for z in ('none','A','B','0','1','2','3')]+[(51,'none')]:
            expected.add(orbit(vals,loc,n));total+=1
    assert len(archive)==len(expected)==64 and {orbit(*r) for r in archive}==expected
    assert set(archive.values())=={'unsat'}
    print(total,'labelled graph/location/order combinations in',len(archive),'orbits, all archived UNSAT',flush=True)
    return sorted(archive)
def controls():
    for loc,nb in [('none',9),('A',9),('B',8),('0',9)]:
        A=set(range(4,11));B=set(range(11,11+nb));V=set(range(11+nb));S=set(range(4));ng={x:set() for x in V}
        def join(i,j):ng[i].add(j);ng[j].add(i)
        def keep(i,c):
            if loc=='A' and i==4 and c==0:return False
            if loc=='B' and i==11 and c in [0,1]:return False
            if loc=='0' and i in B and i>=13 and c==0:return False
            return True
        for side in [A,B]:
            for i,j in combinations(side,2):join(i,j)
            for i,c in product(side,S):
                if keep(i,c):join(i,c)
        low=[x for x in V if len(ng[x])<10]
        assert sorted(map(len,ng.values()))[1]==10
        assert not low if loc=='none' else len(low)==1 and len(ng[low[0]])==9
        D={}
        for root in V:
            d={root:0};q=deque([root])
            while q:
                w=q.popleft()
                for v in ng[w]-d.keys():d[v]=d[w]+1;q.append(v)
            assert len(d)==len(V);D[root]=d
        e=max(sum(v>0 and not v%2 for v in d.values()) for d in D.values())
        assert e<=10
        pattern=''.join(str(D[i][j]) for i,j in pairs)
        actual=Counter(('A' if x in A else 'B',x in low,tuple(D[x][s] for s in range(4))) for x in A|B)
        formula,types=gen(pattern,loc,len(V),20000)
        assert set(actual).issubset(types)
        formula=formula.replace('(check-sat)','\n'.join(f'(assert (= c{i} {actual[t]}))' for i,t in enumerate(types))+'\n(check-sat)')
        assert run(formula)=='sat'
        print('SAT graph control: low',loc,'order',len(V),'second degree 10, max even',e,flush=True)
def solve(k):
    text=subprocess.check_output([sys.executable,str(at/'clique4.py'),*map(str,k),'--timeout','90000'],text=True).strip()
    assert text=='unsat',(k,text)
    return [*k,text]
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--replay',action='store_true');a.add_argument('--workers',type=int,default=2);a=a.parse_args()
    keys=verify();controls()
    if a.replay:
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            for r in ex.map(solve,keys):print(json.dumps(r),flush=True)
        print('64/64 fresh UNSAT.',flush=True)
