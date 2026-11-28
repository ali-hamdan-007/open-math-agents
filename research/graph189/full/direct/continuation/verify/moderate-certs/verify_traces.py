"""Replay a witness without a path search, an enumeration routine, or a constraint solver."""
import json
from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
here=Path(__file__).resolve().parent
def key(a,b):return tuple(sorted((a,b)))
def verify(data, pattern):
    n,p,k=data['n'],data['p'],data['k'];z=n-1
    vertices=set(range(n));req=lambda v:2 if v==z else k
    all_edges=list(combinations(range(n),2))
    lo={e for e in all_edges if (data['lower'][e[0]]>>e[1])&1}
    up={e for e in all_edges if (data['upper'][e[0]]>>e[1])&1}
    from_pattern={key(v,v+1) for v in range(p-1)}
    ext,contacts=pattern['ext'],pattern['contacts']
    for a,row in enumerate(ext):
        for b in range(len(ext)):
            if (row>>b)&1:from_pattern.add(key(p+a,p+b))
        for j in range(p):
            if (contacts[a]>>j)&1:from_pattern.add(key(j,p+a))
        if row.bit_count()+contacts[a].bit_count()==k-1:from_pattern.add(key(z,p+a))
    assert from_pattern==lo
    assert up==lo|{(a,b) for a,b in all_edges if b<p or b==z}
    def path(event,g):
        seq=event['vertices'];scope=event['scope']
        assert scope in ['G','H'] and len(seq)==len(set(seq))
        assert set(seq)<=vertices and all(key(a,b) in g for a,b in zip(seq,seq[1:]))
        assert (len(seq)>=n-(k+1)//2-1 if scope=='G' else z not in seq and len(seq)>=p+1)
    for step in data['steps']:
        a,b=step['a'],step['b'];e=key(a,b)
        assert e in up-lo
        if step['kind']=='forbid':path(step,lo|{e});up.remove(e)
        else:
            assert step['kind']=='force'
            ns={w for w in vertices if key(a,w) in up}
            assert set(step['available'])==ns and len(ns)==req(a)
            lo.add(e)
    end=data['end'];kind=end['kind']
    if kind=='path':path(end,lo);return
    v=end['v']
    if kind=='cut':
        left,right=set(end['left']),set(end['right'])
        assert left and right and not left & right and left|right==vertices-{v}
        assert all(key(a,b) not in up for a in left for b in right)
    elif kind=='degree':
        ns={w for w in vertices if key(v,w) in up}
        assert set(end['available'])==ns and len(ns)<req(v)
    else:
        assert kind=='even'
        ys={y for y,_ in end['pairs']}
        assert v not in ys and len(ys)>k
        assert all(key(v,y) not in up and key(v,m) in lo and key(y,m) in lo for y,m in end['pairs'])
def main():
    for k,expected in [(3,9),(4,30),(5,51),(6,98)]:
        pat=json.loads((here/f'patterns-{k}.json').read_text())
        traces=json.loads((here/f'traces-{k}.json').read_text())
        assert [r['id'] for r in pat]==[r['id'] for r in traces] and len(pat)==expected
        for tr,pr in zip(traces,pat):verify(tr,pr)
        print(k,len(traces),dict(Counter(r['end']['kind'] for r in traces)),sum(len(r['steps']) for r in traces))
if __name__=='__main__':main()
