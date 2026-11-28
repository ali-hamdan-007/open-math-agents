"""Independent labelled enumeration and graph-geodesic check of the two controls."""
from itertools import product, permutations, combinations
from collections import deque,Counter
from pathlib import Path
import json
here=Path(__file__).resolve().parents[2] / 'global' / 'cut3'
edges=list(combinations(range(3),2))
rows={tuple(json.loads(s)[:5]) for s in (here/'deep-cases.jsonl').read_text().splitlines()}
covered=set();seen=0
for big in [0,1]:
    for d in product(range(1,6), repeat=3):
        graph=dict(zip(edges,d))
        dist=lambda a,b: 0 if a==b else graph[tuple(sorted([a,b]))]
        if big and 1 in d:continue
        if any(dist(a,c)>dist(a,b)+dist(b,c) for a,b,c in permutations(range(3))):continue
        for low in ['none','A','B',0,1,2]:
            if any(dist(a,b)>(5 if low in [a,b] else 4) for a,b in edges):continue
            for absent_a,absent_b in product(range(3),repeat=2):
                seen+=1
                candidates=set()
                for perm in permutations(range(3)):
                    if perm.index(absent_b)!=2:continue
                    geom=''.join(str(dist(perm[a],perm[b])) for a,b in edges)
                    lowlab=str(perm.index(low)) if isinstance(low,int) else low
                    key=(geom,lowlab,2,big,perm.index(absent_a))
                    if key in rows:candidates.add(key)
                assert candidates,(d,low,big,absent_a,absent_b)
                covered.update(candidates)
assert covered==rows and len(rows)==1053
print(f'{seen} fully labelled deep cut cases represented by the {len(rows)} archive rows.')
clique_rows={tuple(json.loads(s)[:5]) for s in (here/'exterior-small-degree.jsonl').read_text().splitlines()}
covered=set();seen=0
for d,low,k in product(product((1,2),repeat=3), ['none','A','B',0,1,2],range(8,16)):
    graph=dict(zip(edges,d))
    for perm in permutations(range(3)):
        geom=''.join(str(graph[tuple(sorted([perm[a],perm[b]]))]) for a,b in edges)
        lowlab=str(perm.index(low)) if isinstance(low,int) else low
        key=(geom,lowlab,2,1,k)
        if key in clique_rows:covered.add(key)
    seen+=1
assert covered==clique_rows and len(covered)==192
print(f'{seen} fully labelled narrow-order cases represented in {len(clique_rows)} archive rows.')
for sizes,ports in [([6,8],[6,8]),([17,17],[10,10])]:
    order=3+sum(sizes)
    ng=[set() for _ in range(order)]
    def edge(i,j):ng[i].add(j);ng[j].add(i)
    offset=3
    for size,nports in zip(sizes,ports):
        for i,j in combinations(range(offset,offset+size),2):edge(i,j)
        for i,j in product(range(3),range(offset,offset+nports)):edge(i,j)
        offset+=size
    k=sorted(map(len,ng))[1]; mult=Counter();maximum=0
    for i in range(order):
        D={i:0};q=deque([i])
        while q:
            w=q.popleft()
            for x in ng[w]:
                if x not in D:D[x]=D[w]+1;q.append(x)
        assert len(D)==order
        maximum=max(maximum,sum(v>0 and v%2==0 for v in D.values()))
        if i>=3:mult[(int(i>=3+sizes[0]),tuple(D[a] for a in range(3)))]+=1
    assert maximum<=k
    print('Concrete graph',sizes,ports, 'n,k,max positive even',order,k,maximum,'observed types',dict(mult))
