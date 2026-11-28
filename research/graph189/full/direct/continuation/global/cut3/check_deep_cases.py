"""Manifest and finite replay for the two nonshallow sides of a three-cut."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from collections import Counter,deque
import itertools,json,subprocess,sys
from pathlib import Path
from check_exact_cases import cases as base_cases
from deep_types import build,run_smt
here=Path(__file__).resolve().parent
def replay(job):
    (ds,low,missing_b,big,missing_a),ms=job
    out=subprocess.check_output([sys.executable,str(here/'deep_types.py'),ds,low,str(missing_b),str(big),str(ms),str(missing_a)],text=True)
    return json.loads(out)[-1]
def positive():
    # k=16, two K17s, with 10 simultaneous three-ports and 7 nonports per side.
    dom=range(37);G=[set() for _ in dom]
    for base in (3,20):
        for i,j in itertools.combinations(range(base,base+17),2):G[i].add(j);G[j].add(i)
        for a,x in itertools.product(range(3),range(base,base+10)):G[a].add(x);G[x].add(a)
    dist=[]
    for x in dom:
        d={x:0};queue=deque([x])
        while queue:
            y=queue.popleft()
            for u in G[y]-d.keys():d[u]=d[y]+1;queue.append(u)
        dist.append(d)
    assert sorted(map(len,G))[1]==16
    assert all(sum(y!=x and r%2==0 for y,r in ds.items())<=16 for x,ds in enumerate(dist))
    cnt=Counter((int(x>=20),tuple(dist[x][i] for i in range(3))) for x in range(3,37))
    types=[]
    for s in range(2):
        for v in itertools.product(range(1,5),repeat=3):
            if any(abs(v[i]-v[j])>2 for i,j in itertools.combinations(range(3),2)) or min(v)>2:continue
            if min(v)==2 and v.count(2)==1 and v[2 if s else 0]==2:continue
            types.append((s,v))
    query,n=build((2,2,2),'none',2,0,15000,0)
    assert len(types)==n
    query='\n'.join(s for s in query.splitlines() if '(- (* 5 k) 5)' not in s and s!='(check-sat)')
    query+='\n(assert (= k 16))\n'+'\n'.join(f'(assert (= c{i} {cnt[t]}))' for i,t in enumerate(types))+'\n(check-sat)'
    assert run_smt(query)=='sat'
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--replay',action='store_true');ap.add_argument('--workers',type=int,default=2);ap.add_argument('--timeout-ms',type=int,default=60000);args=ap.parse_args()
    requested={tuple(x)+(i,) for x in base_cases() for i in range(3)}
    rows=[json.loads(s) for s in (here/'deep-cases.jsonl').read_text().splitlines()]
    assert len(rows)==len(requested)==1053 and {tuple(x[:5]) for x in rows}==requested and all(x[-1]=='unsat' for x in rows)
    positive(); print('All 1053 case identities, stored UNSAT statuses and the concrete qualifying deep-side SAT control passed.',flush=True)
    if args.replay:
        jobs=[(case,args.timeout_ms) for case in sorted(requested)]
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for (case,_),answer in zip(jobs,pool.map(replay,jobs)):
                if answer!='unsat':raise RuntimeError((case,answer))
        print('All 1053 exact real-linear decision problems returned UNSAT on replay.')
