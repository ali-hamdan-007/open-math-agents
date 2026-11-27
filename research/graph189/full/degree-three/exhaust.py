from itertools import combinations,combinations_with_replacement,permutations
from functools import lru_cache
from collections import Counter
import sys
from seek import search
K=int(sys.argv[1]); captime=int(sys.argv[2]); threshold=3*K
def perm(x,p):
 return sum(1<<p[i] for i in range(3) if x>>i&1)
counts=Counter()
for am in (0,1,3,7):
 pairs=list(combinations(range(3),2))
 n=[0]*3
 for j,(x,y) in enumerate(pairs):
  if am>>j&1:n[x]|=1<<y;n[y]|=1<<x
 perms=[p for p in permutations(range(3)) if all(n[p[i]]==perm(n[i],p) for i in range(3))]
 for b in range(max(1,K-3),K+1):
  for m in combinations_with_replacement(range(1,8),b):
   if any(tuple(sorted(perm(x,p) for x in m))<m for p in perms):continue
   if any(1+n[i].bit_count()+sum(x>>i&1 for x in m)<K for i in range(3)):continue
   counts['sym profiles']+=1
   fixed=[2-n[i].bit_count()+sum(1 for x in m if not(x>>i&1) and x&n[i]) for i in range(3)]
   cap=tuple(K-j for j in fixed)
   @lru_cache(None)
   def maxc(c):
    ds=[tuple(v-((mask>>i)&1) for i,v in enumerate(c)) for mask in set(m)]
    return max([0]+[1+maxc(d) for d in ds if min(d)>=0])
   upper=4+b+maxc(cap)
   for sz in range(threshold+1,upper+1):
    key=(am,m,sz)
    out=search(K,sz,am,m,captime)
    counts[sz,out]+=1
    if out!='unsat':print(key,out,flush=True)
print('counts',counts,flush=True)
