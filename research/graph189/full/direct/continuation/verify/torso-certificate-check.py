import importlib.util
import itertools
from pathlib import Path

spec=importlib.util.spec_from_file_location("torso",Path(__file__).with_name("torso-certificate.py"))
torso=importlib.util.module_from_spec(spec)
spec.loader.exec_module(torso)
for order in range(1,6):
    n=order+1
    whole=(1<<order)-1
    pairs=list(itertools.combinations(range(order),2))
    checked=0
    for code in range(1<<len(pairs)):
        adj=[0]*n
        for index,(u,v) in enumerate(pairs):
            if code & (1<<index):
                adj[u] |= 1<<v
                adj[v] |= 1<<u
        if len(torso.components(adj,whole)) != 1:
            continue
        # For every chosen starting vertex, exhaustively enumerate simple paths.
        maximum=[0]*order
        for root in range(order):
            queue=[(root,1<<root)]
            while queue:
                v,mask=queue.pop()
                maximum[root]=max(maximum[root],mask.bit_count())
                queue.extend((w,mask|(1<<w)) for w in torso.vertices(adj[v]&~mask))
        for ports in range(1,1<<order):
            adj[order]=ports
            actual=max(maximum[i] for i in torso.vertices(ports))
            result=torso.side_bound(adj,ports,whole)
            claimed=result["length"]
            if "path" in result:
                witness=result["path"]
                assert len(witness)==claimed==len(set(witness)) and (1<<witness[0])&ports
                assert all((1<<v)&adj[u] for u,v in zip(witness,witness[1:]))
            assert 1<=claimed<=actual, (order,code,ports,claimed,actual)
            checked+=1
    print(order,checked,flush=True)
# End-to-end test on the degree-11 qualifying counterexample to prescribed r.
S=list(range(7))
A=list(range(7,14))
B=list(range(14,19))
edges=set()
for clique in (S,A[:-1],B):
    edges.update(itertools.combinations(clique,2))
for v in range(6):
    edges.update((min(v,w),max(v,w)) for w in range(19) if v!=w)
edges.update((6,w) for w in [7,*B])
edges.add((7,13))
result=torso.certificate({"n":19,"edges":sorted(edges),"separator":S})
assert result["certified_traceable"] and result["k"]==result["max_positive_even"]==11
print("end-to-end",result["path_certificate"]["length"],result["needed_path_order"])
# Nonqualifying three-leaf star must not certify: use a supplied two-component cut.
star=torso.certificate({"n":4,"edges":[(0,1),(0,2),(0,3)],"separator":[0,1]})
assert not star["qualifies"] and not star["certified_traceable"], star
print("nonqualifying nontraceable case rejected")
# Deliberately branching side: the best rooted path goes through two bridges
# and nontrivial endblocks, abandoning the third branch.
side_edges=[(0,1),(1,2),(2,3),(3,4),(1,5),(5,6),(5,7),(6,7),(1,8),(8,9)]
adj=[0]*10
for u,v in side_edges:
    adj[u]|=1<<v
    adj[v]|=1<<u
branch=torso.side_bound(adj,1<<4,(1<<10)-1)
assert branch["length"]==7, branch
assert torso.block_chain(adj,(1<<10)-1,1<<4)["length"]==7
assert branch["path"][0]==4 and len(set(branch["path"]))==7
print("branched side exact",branch["path"])

# Check the end-to-end result and explicit witness on deterministic graph samples.
import random
rng=random.Random(189)
for trial in range(80):
    n=8+(trial%3)
    S=[0,1,2]
    A=list(range(3,3+(n-3)//2))
    B=list(range(3+(n-3)//2,n))
    edges=set(zip(S,S[1:]))|set(zip(A,A[1:]))|set(zip(B,B[1:]))
    for side in (A,B):
        for anchor in S:
            edges.add((anchor,rng.choice(side)))
        for u,v in itertools.combinations(side,2):
            if rng.randrange(2):
                edges.add((u,v))
    edges=sorted(tuple(sorted(edge)) for edge in edges)
    result=torso.certificate({"n":n,"edges":edges,"separator":S})
    adj=[0]*n
    for u,v in edges:
        adj[u]|=1<<v
        adj[v]|=1<<u
    best=result["path_certificate"]
    if "path" in best:
        seq=best["path"]
        assert len(seq)==best["length"]==len(set(seq))
        assert all(adj[u]&(1<<v) for u,v in zip(seq,seq[1:]))
    if result["certified_traceable"]:
        ends=[0]*(1<<n)
        for v in range(n):
            ends[1<<v]=1<<v
        for mask in range(1,1<<n):
            for u in torso.vertices(ends[mask]):
                for v in torso.vertices(adj[u]&~mask):
                    ends[mask|1<<v] |= 1<<v
        assert ends[-1], (trial,result)
print("80 end-to-end instances compared to exact Hamilton-path DP")
# Connectivity must sometimes use the length-three match rather than just common neighbors.
pentagon=[(1<<((v+1)%5))|(1<<((v-1)%5)) for v in range(5)]
assert torso.short_link_connectivity(pentagon,2)
assert not torso.short_link_connectivity(pentagon,3)
# Three universal vertices joining three disjoint cliques. Degree closure and Fan
# leave vacancies, but the three anchor paths and clique cover certify a full cycle.
sizes=[8,2,2]
big=3+sum(sizes)
adj=[0]*big
gate=(1<<3)-1
for i in range(3):
    adj[i]=((1<<big)-1)^(1<<i)
first=3
for size in sizes:
    group=((1<<size)-1)<<first
    for v in range(first,first+size):
        adj[v]=(gate|group)^(1<<v)
    first+=size
proof=torso.circumference(adj)
assert proof["bound"]==big and proof["test"]=="Chvatal-Erdos via short disjoint paths",proof
print("short-link connectivity and independent three-clique certificate validated")
