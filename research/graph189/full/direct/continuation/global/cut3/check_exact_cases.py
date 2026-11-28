"""Validate the archived case set, positive control, and optional standalone replays."""
import argparse
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
import itertools
import subprocess
import sys
import json
from pathlib import Path
from exact_types import build,run_smt
here=Path(__file__).resolve().parent
def cases():
    for big in [0,1]:
        for ds in itertools.product(range(1+big,6),repeat=3):
            d,e,f=ds
            if e>f or 2*max(ds)>sum(ds):continue
            for low in ['none','A','B','0','1','2']:
                if e==f and low=='1':continue
                if any(w>4 and low not in edge for w,edge in zip(ds,['01','02','12'])):continue
                yield (''.join(map(str,ds)),low,2,big)
def positive():
    """Two 15-cliques with each of 3 two-anchor supports appearing 5 times per side."""
    dom=list(range(33)); G=[set() for _ in dom]
    for left in (3,18):
        for x,y in itertools.combinations(range(left,left+15),2):
            G[x].add(y);G[y].add(x)
        for j,x in enumerate(range(left,left+15)):
            for a in range(3):
                if a!=j//5:G[a].add(x);G[x].add(a)
    dist=[]
    for x in dom:
        d={x:0}; work=deque([x])
        while work:
            y=work.popleft()
            for v in G[y]-d.keys():d[v]=d[y]+1;work.append(v)
        dist.append(d)
    assert sorted(map(len,G))[1]==16
    assert all(sum(v!=x and d%2==0 for v,d in dist[x].items())<=16 for x in dom)
    counts=Counter((0 if x<18 else 1,tuple(dist[x][a] for a in range(3))) for x in range(3,33))
    assert sum(counts.values())==30
    typ=[]
    for side in (0,1):
        for v in itertools.product(range(1,5),repeat=3):
            if any(abs(v[i]-v[j])>2 for i,j in itertools.combinations(range(3),2)):continue
            if side==0 and (min(v)!=1 or v==(1,1,1)):continue
            if side==1 and (min(v)>2 or (min(v)==2 and v.count(2)==1 and v[2]==2)):continue
            typ.append((side,v))
    query,n=build((2,2,2),'none',2,0,10000)
    assert n==len(typ) and len(counts)==6
    query='\n'.join(s for s in query.splitlines() if '(- (* 5 k) 5)' not in s and s!='(check-sat)')
    query+='\n(assert (= k 16))\n'+'\n'.join(f'(assert (= c{i} {counts[t]}))' for i,t in enumerate(typ))+'\n(check-sat)'
    assert run_smt(query)=='sat'
def replay(job):
    (ds,low,absent,big),timeout=job
    command=[sys.executable,str(here/'exact_types.py'),ds,low,str(absent),str(big),str(timeout)]
    return json.loads(subprocess.check_output(command,text=True))[-1]
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--replay',action='store_true');ap.add_argument('--workers',type=int,default=2);ap.add_argument('--timeout-ms',type=int,default=60000)
    args=ap.parse_args(); requested=set(cases())
    rows=[json.loads(s) for s in (here/'exact-cases.jsonl').read_text().splitlines()]
    assert len(rows)==len(requested)==351
    assert {tuple(x[:4]) for x in rows}==requested and all(x[-1]=='unsat' for x in rows)
    positive()
    print('Canonical coverage, stored UNSAT statuses, concrete graph and SAT control passed.')
    if args.replay:
        jobs=[(case,args.timeout_ms) for case in sorted(requested)]
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for (case,_),answer in zip(jobs,pool.map(replay,jobs)):
                if answer!='unsat':raise RuntimeError((case,answer))
        print('All 351 exact real-linear decision problems returned UNSAT on replay.')
