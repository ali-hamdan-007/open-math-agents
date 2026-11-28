from itertools import product, combinations
from collections import Counter,deque
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'global' / 'cut3'))
from small_three_types import build,run_smt
check=[]
for internal in [False,True]:
    blocks=[range(3,12),range(12,22)]
    ng=[set() for i in range(22)]
    def edge(x,y):ng[x].add(y);ng[y].add(x)
    for block,portcount in zip(blocks,[8,7]):
        for x,y in combinations(block,2):edge(x,y)
        for x,y in product(range(3),block[:portcount]):edge(x,y)
    if internal:edge(0,1)
    degs=list(map(len,ng));k=sorted(degs)[1];assert k==9 and degs.count(8)==1 and min(degs)==8
    V=range(22);low=degs.index(min(degs));assert low in blocks[0]
    dist=[]
    for x in V:
        d={x:0};q=deque([x])
        while q:
            v=q.popleft()
            for w in ng[v]:
                if w in d:continue
                d[w]=d[v]+1;q.append(w)
        assert len(d)==22
        dist.append(d)
    ev=max(sum(d[x]>0 and d[x]%2==0 for x in V) for d in dist);assert ev==8
    ed=list(combinations(range(3),2))
    geo=tuple(dist[a][b] for a,b in ed)
    cnt=Counter((a,int(x==low),tuple(dist[x][i] for i in range(3))) for a,B in enumerate(blocks) for x in B)
    types=[]
    for a in range(2):
        for l in ([0,1] if a==0 else [0]):
            for v in product(range(1,6 if l else 5),repeat=3):
                if all(abs(v[i]-v[j])<=dist[i][j]<=v[i]+v[j] for i,j in ed) and min(v)<=(4 if l else 3):
                    types.append((a,l,v))
    assert set(cnt)<=set(types)
    full,n=build(geo,'A',2,0,15000,9)
    assert n==len(types)
    lines=full.splitlines(); toss=[line for line in lines if '(- (* 5 k) 5)' in line]
    assert len(toss)==1
    restricted='\n'.join(line for line in lines if line not in toss and line!='(check-sat)')
    restricted+='\n'+'\n'.join(f'(assert (= c{i} {cnt[t]}))' for i,t in enumerate(types))+'\n(check-sat)'
    assert run_smt(restricted)=='sat'
    print('graph order 22, second degree 9, unique low degree 8 in A, max positive even 8, anchor triangle',geo,'SAT after removing precisely the order lower bound')
