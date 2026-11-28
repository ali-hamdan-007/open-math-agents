"""Validate and independently replay the unrestricted k=9..15 three-cut relaxation."""
import argparse,itertools,json,subprocess,sys
from concurrent.futures import ThreadPoolExecutor
from collections import Counter,deque
from pathlib import Path
from small_three_types import build,run_smt
here=Path(__file__).resolve().parent
def cases():
    for ds in itertools.combinations_with_replacement(range(1,6),3):
        if max(ds)*2>sum(ds):continue
        for low in ['none','A','B','0','1','2']:
            if any(d>4 and low not in pair for d,pair in zip(ds,['01','02','12'])):continue
            for k,big in itertools.product(range(9,16),(0,1)):yield (''.join(map(str,ds)),low,2,big,k)
def positive():
    # Two K9s; each side has three of each two-anchor support; k=10.
    G=[set() for _ in range(21)]
    for start in [3,12]:
        for x,y in itertools.combinations(range(start,start+9),2):G[x].add(y);G[y].add(x)
        for x,a in itertools.product(range(start,start+9),range(3)):
            if (x-start)//3!=a:G[x].add(a);G[a].add(x)
    D=[]
    for x in range(21):
        d={x:0};q=deque([x])
        while q:
            u=q.popleft()
            for y in G[u]-d.keys():d[y]=d[u]+1;q.append(y)
        D.append(d)
    assert sorted(map(len,G))[1]==10 and all(sum(v!=x and n%2==0 for v,n in a.items())<=10 for x,a in enumerate(D))
    counts=Counter((int(x>=12),tuple(D[x][i] for i in range(3))) for x in range(3,21))
    typ=[(t,v) for t in range(2) for v in itertools.product(range(1,5),repeat=3) if min(v)<=3 and max(v)-min(v)<=2]
    query,n=build((2,2,2),'none',2,0,10000,10);assert n==len(typ)
    query='\n'.join(s for s in query.splitlines() if '(- (* 5 k) 5)' not in s and s!='(check-sat)')
    query+='\n'+'\n'.join(f'(assert (= c{j} {counts[t]}))' for j,t in enumerate(typ))+'\n(check-sat)'
    assert run_smt(query)=='sat'
def replay(job):
    (d,l,m,b,k),tm=job
    return json.loads(subprocess.check_output([sys.executable,str(here/'small_three_types.py'),d,l,str(m),str(b),str(tm),str(k)],text=True))[-1]
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--replay',action='store_true');p.add_argument('--timeout-ms',type=int,default=60000);p.add_argument('--workers',type=int,default=2);opt=p.parse_args()
    keys=set(cases());rows=[json.loads(s) for s in (here/'small-three-cases.jsonl').read_text().splitlines()]
    assert len(keys)==len(rows)==1652 and {tuple(r[:5]) for r in rows}==keys and all(r[-1]=='unsat' for r in rows)
    positive();print('All 1652 case identities, stored UNSAT statuses and the concrete k=10 SAT control passed.',flush=True)
    if opt.replay:
        jobs=[(k,opt.timeout_ms) for k in sorted(keys)]
        with ThreadPoolExecutor(max_workers=opt.workers) as pool:
            for (k,_),out in zip(jobs,pool.map(replay,jobs)):
                if out!='unsat':raise RuntimeError((k,out))
        print('All 1652 exact real-linear problems returned UNSAT on replay.')
