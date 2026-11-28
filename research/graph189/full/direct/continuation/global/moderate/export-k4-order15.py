"""Export the 72 pre-completion rows from the independent degree-window program."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json,subprocess
from collections import Counter

here=Path(__file__).resolve().parent
verify=here.parents[1]/'verify'
marker='void complete(Graph fixed,int p,int k,Totals &tot,bool saturatedShell=false){'
code=(verify/'degree-window-engine.cpp').read_text(); assert code.count(marker)==1
with TemporaryDirectory() as td:
    d=Path(td)
    (d/'degree-window-engine.cpp').write_text(code.replace(marker,marker+' cout<<"ROW "<<p; for(auto r:fixed) cout<<" "<<r; cout<<endl; return;'))
    (d/'driver.cpp').write_bytes((verify/'small-degree-independent.cpp').read_bytes())
    subprocess.run(['c++','-O2','-std=c++17','driver.cpp','-o','enum'],cwd=d,check=True)
    lines=subprocess.check_output(['./enum','4','15','15'],cwd=d,text=True).splitlines()
records=[]
for line in lines:
    if not line.startswith('ROW '):continue
    p,*lo=map(int,line.split()[1:]); b=14-p
    records.append(dict(n=15,p=p,b=b,lower=lo))
records.sort(key=lambda r:(r['b'],r['lower']))
for id,r in enumerate(records):r['id']=id
assert len(records)==len({tuple(r['lower']) for r in records})==72
(here/'k4-order15-rows.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
shapes=Counter()
for r in records:
    p,b,L=r['p'],r['b'],r['lower']; M=[L[v] & ((1<<p)-1) for v in range(p,14)]; X=[L[v]>>p & ((1<<b)-1) for v in range(p,14)];tc=0
    for q in M:tc|=q
    shapes[(p,b,tuple(sorted(v.bit_count() for v in X)),tc.bit_count())]+=1
print(shapes)
