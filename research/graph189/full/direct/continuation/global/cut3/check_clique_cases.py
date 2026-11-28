"""Verify or replay the bounded final exterior-clique cases."""
import argparse, itertools, json, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from clique_types import build,run_smt
here=Path(__file__).resolve().parent
def check(job):
    x,timeout=job
    ds,low,absent,big,k=x
    return json.loads(subprocess.check_output([sys.executable,str(here/'clique_types.py'),ds,low,str(absent),str(big),str(timeout),str(k)],text=True))[-1]
def positive():
    # K6 and K8, both complete to three independent separator vertices.
    # The high types on both sides are exactly 111; the anchor d-matrix is all 2.
    q,_=build((2,2,2),'none',2,1,5000,8)
    q='\n'.join(s for s in q.splitlines() if not any(t in s for t in ['(- (* 5 k) 7)','(- (* 5 k) 6)',' (* 3 k))','(check-sat)']))
    # A has just one allowed type (111), and 111 is first on B by construction.
    q+='\n(assert (= c0 6))\n(assert (= c1 8))'
    import re
    for idx in re.findall(r'\(declare-const c(\d+) Real\)',q):
        if int(idx)>1:q+=f'\n(assert (= c{idx} 0))'
    assert run_smt(q+'\n(check-sat)')=='sat'
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--replay',action='store_true');ap.add_argument('--workers',type=int,default=2);ap.add_argument('--timeout-ms',type=int,default=60000);args=ap.parse_args()
    cases={(ds,low,2,1,k) for ds,low,k in itertools.product(['111','112','122','222'],['none','A','B','0','1','2'],range(8,16))}
    stored=[json.loads(s) for s in (here/'exterior-small-degree.jsonl').read_text().splitlines()]
    assert len(cases)==len(stored)==192 and {tuple(r[:5]) for r in stored}==cases and all(r[-1]=='unsat' for r in stored)
    positive(); print('Verified all 192 case identities, stored UNSAT statuses, and the concrete two-clique SAT control.',flush=True)
    if args.replay:
        jobs=[(r,args.timeout_ms) for r in sorted(cases)]
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for (r,_),result in zip(jobs,pool.map(check,jobs)):
                if result!='unsat':raise RuntimeError((r,result))
        print('All 192 exact queries returned UNSAT on replay.')
