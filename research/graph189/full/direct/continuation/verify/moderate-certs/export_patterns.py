"""Collect adjacency masks from the independent canonical generator before propagation."""
from pathlib import Path
import subprocess,tempfile
from collections import defaultdict
import json
here=Path(__file__).resolve().parent
source=(here/'attachment-enumerator.cpp').read_text()
point='void complete(Graph fixed,int p,int k,Totals &tot){'
assert source.count(point)==1
probe='''
  ++tot.raw;
  cout<<"ROW "<<k<<" "<<p;
  for(Row r:fixed)cout<<" "<<r;
  cout<<endl;
  return;
'''
with tempfile.TemporaryDirectory() as tmp:
    src=Path(tmp)/'emit.cpp'
    exe=Path(tmp)/'emit'
    src.write_text(source.replace(point,point+probe))
    subprocess.run(['g++','-std=c++17','-O2',str(src),'-o',str(exe)],check=True)
    output=subprocess.check_output([str(exe),'6'],text=True)
records=defaultdict(list)
for line in output.splitlines():
    if line.startswith('ROW '):
        k,p,*rows=map(int,line.split()[1:])
        n=len(rows);b=n-p-1
        ext=[(r>>p)&((1<<b)-1) for r in rows[p:-1]]
        marks=[r&((1<<p)-1) for r in rows[p:-1]]
        records[k].append(dict(k=k,p=p,n=n,b=b,ext=ext,contacts=marks,lower=rows))
for k,rows in records.items():
    rows.sort(key=lambda r:(r['b'],r['p'],r['ext'],r['contacts']))
    for idx,row in enumerate(rows):row['id']=f'k{k}p{idx:03d}'
    (here/f'patterns-{k}.json').write_text(json.dumps(rows,indent=1)+'\n')
    print(k,len(rows))
