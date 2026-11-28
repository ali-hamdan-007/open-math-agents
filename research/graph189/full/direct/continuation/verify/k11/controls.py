"""BFS-check graphs and impose all their true type counts on the model."""
from collections import deque,Counter
from itertools import product,combinations
from k11 import gen,run
for size,loc in [(8,'none'),(8,'A'),(8,'B'),(8,'0'),(9,'none'),(9,'A')]:
    nb=9 if loc in ['B','0'] or (size==9 and loc=='A') else 10
    S=set(range(4));A=set(range(4,4+size));B=set(range(4+size,4+size+nb));V=A|B|S
    ng={x:set() for x in V}
    def link(x,y):ng[x].add(y);ng[y].add(x)
    def attached(x,i):
        if size==9 and x in A:
            if loc=='A' and x==4:return i not in (0,1)
            return (x-4)%(2 if loc=="A" else 4)!=i
        if loc=='A' and x==4:return i!=0
        if loc=='B' and x==min(B):return i not in (0,1)
        if loc=='0' and x in B and i==0:return x<min(B)+2
        return True
    for side in (A,B):
        for x,y in combinations(side,2):link(x,y)
        for x,i in product(side,S):
            if attached(x,i):link(x,i)
    low=[x for x in V if len(ng[x])<11]
    assert sorted(map(len,ng.values()))[1]==11
    assert not low if loc=='none' else len(low)==1 and len(ng[low[0]])==10
    measured={}
    for x in V:
        d={x:0};q=deque([x])
        while q:
            u=q.popleft()
            for v in ng[u]-d.keys():d[v]=d[u]+1;q.append(v)
        measured[x]=d
    e=max(sum(j>0 and j%2==0 for j in d.values()) for d in measured.values());assert e<=11
    ed=''.join(str(measured[i][j]) for i,j in combinations(range(4),2))
    pop=Counter(('A' if x in A else 'B',x in low,tuple(measured[x][i] for i in range(4))) for x in A|B)
    formula,types=gen(ed,loc,58,size,20000,override_b=nb)
    assert set(pop)<=set(types)
    q=formula.replace('(check-sat)','\n'.join(f'(assert (= c{j} {pop[t]}))' for j,t in enumerate(types))+'\n(check-sat)')
    assert run(q)=='sat'
    print(size,loc,'n',len(V),'second degree 11','max even',e,'fixed BFS populations SAT')
