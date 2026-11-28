"""Return one witnessed catalogue row and a relabeling back to it for every surviving input."""
import json, gzip
from pathlib import Path
from itertools import permutations
here=Path(__file__).resolve().parent
def flip(x,n):return sum(1<<(n-1-j) for j in range(n) if x>>j&1)
def main():
    for k in range(3,7):
        table={}
        for r in json.loads((here/f'patterns-{k}.json').read_text()):
            n=r['b'];p=r['p'];g=r['ext'];A=r['contacts']
            for perm in permutations(range(n)):
                # New exterior vertex i denotes original exterior vertex perm[i].
                eg=tuple(sum(1<<j for j in range(n) if g[perm[i]]>>perm[j]&1) for i in range(n))
                contacts=tuple(A[i] for i in perm)
                for rev,marks in [(False,contacts),(True,tuple(flip(x,p) for x in contacts))]:
                    key=(p,eg,marks)
                    if key not in table:table[key]=r['id'],perm,rev
        rows=[dict(p=p,ext=g,contacts=marks,certificate=ident,exteriorToCertificate=perm,reversePath=rev)
              for (p,g,marks),(ident,perm,rev) in sorted(table.items())]
        raw=(json.dumps(rows,separators=(',',':'))+'\n').encode()
        if k==3:(here/f'orbit-keys-{k}.json').write_bytes(raw)
        else:(here/f'orbit-keys-{k}.json.gz').write_bytes(gzip.compress(raw,mtime=0))
        print(k,len(rows))
if __name__=='__main__':main()
