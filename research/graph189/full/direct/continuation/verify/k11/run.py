from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import argparse,json,sys,subprocess
from k11 import cases
here=Path(__file__).resolve().parent
a=argparse.ArgumentParser();a.add_argument('--timeout',type=int,default=10000);a.add_argument('--workers',type=int,default=4);a.add_argument('--retry');opts=a.parse_args()
def job(k):
    out=subprocess.check_output([sys.executable,str(here/'k11.py'),*map(str,k),'--timeout',str(opts.timeout)],text=True).strip()
    return [*k,out]
keys=list(cases()) if not opts.retry else [json.loads(line)[:-1] for line in Path(opts.retry).read_text().splitlines() if json.loads(line)[-1]=='unknown']
if __name__=='__main__':
    with ThreadPoolExecutor(max_workers=opts.workers) as ex:
        for done in as_completed([ex.submit(job,k) for k in keys]):print(json.dumps(done.result()),flush=True)
