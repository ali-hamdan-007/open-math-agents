"""Test fixed order windows using only exterior components with a possible attachment.

An attached vertex starts no exterior path on more than floor((p-1)/2)
vertices, by replacing either end of the longest path of order p. Existence
of such a vertex is preserved on some connected one-vertex deletion:
delete a leaf distinct from the witness in a spanning tree rooted at it.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement
import argparse
from moderate_exterior_search import bits, canonical, investigate, path_lengths


@lru_cache(maxsize=None)
def has_short_root(rows, cap):
    if len(rows) <= cap:
        return True
    @lru_cache(maxsize=None)
    def long_from(v, used):
        if used.bit_count() > cap:
            return True
        return any(long_from(w, used | (1 << w)) for w in bits(rows[v] & ~used))
    return any(not long_from(v, 1 << v) for v in range(len(rows)))


@lru_cache(maxsize=None)
def connected_types(size, cap):
    if size == 1:
        return [(0,)]
    types = {}
    for old in connected_types(size-1, cap):
        for mask in range(1, 1 << (size-1)):
            extended = tuple(r | ((1 << (size-1)) if (mask & (1<<i)) else 0)
                             for i,r in enumerate(old)) + (mask,)
            # A feasible connected final graph has at least one feasible connected parent.
            if has_short_root(extended, cap):
                key = canonical(extended)
                if key not in types:
                    types[key] = extended
    has_short_root.cache_clear()
    return list(types.values())


def exterior_types(b, cap, degree_floor):
    def partitions(total, lower):
        if not total:
            yield []
        for size in range(lower,total+1):
            if 1 < size <= degree_floor:
                continue
            for other in partitions(total-size, max(2, size)):
                yield [size]+other
    def copies(groups):
        if not groups:
            yield ()
            return
        size,count = groups[0]
        permitted = (rows for rows in connected_types(size,cap)
                     if size==1 or min(r.bit_count() for r in rows)>=degree_floor)
        for family in combinations_with_replacement(permitted,count):
            first=()
            for comp in family:
                shift=len(first)
                first += tuple(r<<shift for r in comp)
            for rest in copies(groups[1:]):
                yield first + tuple(r<<len(first) for r in rest)
    for sizes in partitions(b,1):
        yield from copies(tuple(Counter(sizes).items()))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('k', type=int)
    parser.add_argument('minimum', type=int)
    parser.add_argument('maximum', type=int)
    args=parser.parse_args()
    k=args.k
    h=(k+1)//2
    total=Counter()
    for n in range(args.minimum, args.maximum+1):
        counts=Counter()
        examples=[]
        for b in range(h+1,n-2*k+1):
            p=n-b-1
            seen=0
            for rows in exterior_types(b,(p-1)//2,h-1):
                seen+=1
                investigate(k,p,rows,path_lengths(rows),counts,examples,True,saturated=True)
            print(f'n={n} p={p} b={b} exteriors={seen} cumulative={dict(counts)}',flush=True)
        print(f'n={n} results={dict(counts)} examples={examples}',flush=True)
        total.update(counts)
    if total['surviving patterns']:
        raise SystemExit('unresolved completion patterns')

if __name__=='__main__':
    main()
