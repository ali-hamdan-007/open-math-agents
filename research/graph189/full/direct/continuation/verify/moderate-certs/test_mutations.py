"""Each independent single-field corruption must invalidate its concrete proof."""
from pathlib import Path
import copy,json
from verify_traces import verify
here=Path(__file__).resolve().parent
for k in range(3,7):
    patterns=json.loads((here/f'patterns-{k}.json').read_text())
    traces=json.loads((here/f'traces-{k}.json').read_text())
    attempted=0
    def reject(row):
        global attempted
        try:verify(row,pattern)
        except AssertionError:attempted+=1;return
        raise ValueError(f'accepted corrupted proof {row["id"]}')
    for trace,pattern in zip(traces,patterns):
        if trace['steps']:
            row=copy.deepcopy(trace);w=row['steps'][0]['vertices'];w[0]=w[1];reject(row)
        row=copy.deepcopy(trace);e=row['end']
        if e['kind']=='path':e['vertices'][0]=e['vertices'][1]
        elif e['kind']=='cut':e['left'].append(e['right'][0])
        elif e['kind']=='degree':e['available'].append(e['v'])
        elif e['kind']=='even':e['pairs'][0][0]=e['pairs'][1][0]
        reject(row)
    print(k,attempted,'corrupted proofs rejected')
