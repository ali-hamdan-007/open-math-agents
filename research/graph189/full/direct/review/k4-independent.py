"""Independent exhaustive verification at tied second degree four, n >= 15."""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path

DIR = Path(__file__).resolve().parent.parent
assert (DIR / "LIVE").exists() and not any((DIR / p).exists() for p in ("PAUSE", "HALT"))
pairs = list(combinations(range(4), 2))
perms = tuple(permutations(range(4)))
def mask_set(mask):
    return tuple(i for i in range(mask.bit_length()) if (mask >> i) & 1)
def relabel(mask, perm):
    return sum(1 << perm[i] for i in mask_set(mask))
def graph_relabel(edges, perm):
    return tuple(sorted(tuple(sorted((perm[i], perm[j]))) for i,j in edges))
def weak_compositions(total, width):
    if width == 1:
        yield (total,)
    else:
        for first in range(total+1):
            for tail in weak_compositions(total-first, width-1):
                yield (first,)+tail
cases = set()
seven = 0
for graph_mask in range(64):
    edges = tuple(pairs[i] for i in mask_set(graph_mask))
    images = tuple(graph_relabel(edges,p) for p in perms)
    if edges != min(images):continue
    stabilizer = [p for p,ee in zip(perms,images) if ee==edges]
    adj = [set() for _ in range(4)]
    for i,j in edges: adj[i].add(j);adj[j].add(i)
    for b in range(1,5):
        allotments = {c:list(weak_compositions(c,b)) for c in (6,7)}
        for masks in combinations_with_replacement(range(1,16), b):
            ports = [{j for j,m in enumerate(masks) if m >> i & 1} for i in range(4)]
            if any(1+len(ports[i])+len(adj[i])<4 for i in range(4)):continue
            budget = [4-(3-len(adj[i]))-len(set().union(*(ports[j] for j in adj[i]))-ports[i]) for i in range(4)]
            if any(z<0 for z in budget):continue
            for c,choices in allotments.items():
                for weights in choices:
                    if any(sum(weights[j] for j in ports[i])>budget[i] for i in range(4)):continue
                    if c==7:seven+=1;continue
                    key = min(tuple(sorted((relabel(m,p),u) for m,u in zip(masks,weights))) for p in stabilizer)
                    cases.add((edges,key))
print("Seven allocations",seven,"six-allocation profiles",len(cases),flush=True)
assert seven==0
N=15
full=(1<<N)-1
def add(table,i,j,flag):
    if flag:
        table[i]|=1<<j;table[j]|=1<<i
    else:
        table[i]&=~(1<<j);table[j]&=~(1<<i)
def horizon(table,root,steps):
    seen=1<<root
    front=seen
    for _ in range(steps):
        ext=0
        for v in mask_set(front):ext|=table[v]
        front=ext&~seen
        seen|=front
    return seen
def violates(lo,hi):
    if min(x.bit_count() for x in hi)<4 or sum(x.bit_count()<=4 for x in lo)<2:return True
    for i in range(N):
        forced2=horizon(lo,i,2)&~((1<<i)|hi[i])
        near=horizon(hi,i,3)
        far=full^near
        if (far|forced2).bit_count()>4:return True
        if any(not(hi[j]&near) for j in mask_set(far)):return True
    return False
nodes=0
def search(lo,hi):
    global nodes
    nodes+=1
    if violates(lo,hi):return 0
    # First examine edges incident to vertices whose maximum possible degree is tight.
    moves=[(i,j) for i in range(N) for j in range(i) if (hi[i]^lo[i])>>j&1]
    if not moves:return 1
    moves.sort(key=lambda p:(min(hi[p[0]].bit_count(),hi[p[1]].bit_count()),-(lo[p[0]]|lo[p[1]]).bit_count()))
    for i,j in moves:
        if hi[i].bit_count()==4 or hi[j].bit_count()==4:
            add(lo,i,j,True)
            return search(lo,hi)
    # In unit propagation, process a single newly learned literal and start over.
    for i,j in moves:
        without=hi.copy()
        add(without,i,j,False)
        if violates(lo,without):
            add(lo,i,j,True)
            return search(lo,hi)
        with_edge=lo.copy()
        add(with_edge,i,j,True)
        if violates(with_edge,hi):
            return search(lo,without)
    i,j=moves[0]
    without=hi.copy();add(without,i,j,False)
    with_edge=lo.copy();add(with_edge,i,j,True)
    return search(with_edge,hi.copy())+search(lo.copy(),without)
for edges,profile in sorted(cases):
    b=len(profile)
    layers=[0]+[1]*4+[2]*b+[3]*6+[4]*(4-b)
    lo=[0]*N;hi=[0]*N
    for i,j in combinations(range(N),2):
        if layers[j]-layers[i]<=1:add(hi,i,j,True)
    for j in range(1,5):add(lo,0,j,True)
    for i,j in pairs:
        if (i,j) in edges:add(lo,i+1,j+1,True)
        else:add(hi,i+1,j+1,False)
    tail=b+5
    for col,(mask,amount) in enumerate(profile,5):
        for i in range(4):
            if (mask>>i)&1:add(lo,i+1,col,True)
            else:add(hi,i+1,col,False)
        for j in range(tail,tail+amount):add(lo,col,j,True)
        tail+=amount
    if search(lo,hi):
        raise AssertionError((edges,profile))
print("zero admissible completions, search calls",nodes,flush=True)
