import itertools,json
from pathlib import Path
root=Path(__file__).parent
pairs=list(itertools.combinations(range(4),2));perm=list(itertools.permutations(range(4)));n=0;expected=set()
for size,values,orders in [(9,'12',range(62,68)),(10,'123',range(64,68))]:
    for vals in itertools.product(values,repeat=6):
        dd=dict(zip(pairs,vals))
        def d(i,j):return int(dd[tuple(sorted((i,j)))])
        if any(d(i,j)>d(i,k)+d(k,j) for i,j,k in itertools.permutations(range(4),3)):continue
        under=[(''.join(str(d(s[i],s[j])) for i,j in pairs),s) for s in perm]
        for order in orders:
            for l in (['none','A','B','0','1','2','3'] if order<67 else ['none']):
                n+=1
                expected.add(min((a,str(sig.index(int(l))) if l in '0123' else l,order,size) for a,sig in under))
archive=[json.loads(s) for s in (root/'cases.jsonl').read_text().splitlines()]
assert len(archive)==len(expected)==1095 and set(tuple(x[:-1]) for x in archive)==expected and all(x[-1]=='unsat' for x in archive)
fresh=[json.loads(s) for s in (root/'fresh.jsonl').read_text().splitlines()]
assert len(fresh)==len(expected) and all(x[-1]=='unsat' for x in fresh) and set(tuple(x[:-1]) for x in fresh)==expected
print(n,'labelled cases; 1,095 archive cases and 1,095 fresh cases all UNSAT')
