"""Exhaust the constructive rooted Ore criterion on all graphs through six vertices."""
import itertools
import importlib.util
from pathlib import Path

spec=importlib.util.spec_from_file_location("torso",Path(__file__).with_name("torso-certificate.py"))
torso=importlib.util.module_from_spec(spec)
spec.loader.exec_module(torso)
for n in range(1,7):
    edges=list(itertools.combinations(range(n),2))
    connected=rooted=covered=0
    for code in range(1<<len(edges)):
        adj=[0]*n
        for i,(u,v) in enumerate(edges):
            if code&(1<<i):
                adj[u]|=1<<v
                adj[v]|=1<<u
        if len(torso.components(adj,(1<<n)-1))!=1:
            continue
        connected+=1
        if n>=3:
            cycle=torso.cycle_from_closure(adj)
            if cycle is not None:
                assert len(cycle)==len(set(cycle))==n
                assert all(adj[cycle[i]]&(1<<cycle[(i+1)%n]) for i in range(n))
        defective_endpoints=[]
        for w in range(n):
            for u,v in itertools.combinations(torso.vertices(adj[w]),2):
                if adj[u]&(1<<v):
                    continue
                if (adj[u]|adj[w]|adj[v]).bit_count() > adj[u].bit_count()+adj[v].bit_count():
                    defective_endpoints.append((u,v))
        for root in range(n):
            seq=torso.rooted_ore_path(adj,root)
            assert seq[0]==root and len(seq)==len(set(seq))
            assert all(adj[u]&(1<<v) for u,v in zip(seq,seq[1:]))
            if all(root in pair for pair in defective_endpoints):
                rooted+=1
                assert len(seq)==n,(n,code,root,seq)
            covered+=len(seq)==n
    print(n,connected,rooted,covered,flush=True)
