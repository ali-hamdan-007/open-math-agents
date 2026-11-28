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
