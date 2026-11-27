from pathlib import Path
import sys,subprocess,re,itertools,concurrent.futures
binary=Path(__file__).resolve().parents[1] / "search160"
shape=(0,2,14,16)
seed=''.join('1' if p in shape else '?' for p in range(17))
def job(z):
 n,x=z
 if x+16>=n:return
 out=subprocess.run([str(binary),seed,str(n),str(x)],capture_output=True,text=True)
 m=re.search(r'sat=(\d+), calls=(\d+)',out.stderr)
 if m and m[1]=='0':
  starts=set(range(x,x+161-n))
  starts|={143-a for a in starts}
  eligible=sorted(a//13 for a in starts if a%13==0 and a//13<=5)
  if eligible:print(n,x,int(m[2]),eligible,flush=True)
queue=list(itertools.product([125,130,135,138,140,142,145,147,150,155,160],range(24,75,2)))
queue += list(itertools.product([130,134,138,140,142,145,147,150,155,160],range(0,66,13)))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as x:
 list(x.map(job,queue))
