"""Enumerate a finite relaxation of the small moderate-degree problem.

Each input is a possible exterior graph of a longest path after deleting the
one possible low vertex. All path indices are zero based. Surviving records
are partial specifications, not examples of the original conjecture.
"""
import argparse
import itertools
import json
from collections import Counter
from functools import lru_cache


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def canonical(rows):
    n = len(rows)
    colors = [row.bit_count() for row in rows]
    while True:
        signatures = [(colors[i], tuple(sorted(colors[j] for j in bits(row))))
                      for i, row in enumerate(rows)]
        order = {key: i for i, key in enumerate(sorted(set(signatures)))}
        refined = [order[key] for key in signatures]
        if refined == colors:
            break
        colors = refined
    groups = [[v for v in range(n) if colors[v] == c] for c in sorted(set(colors))]
    permutations = []
    for group in groups:
        twin = all((rows[a] ^ rows[b]) & ~((1 << a) | (1 << b)) == 0
                   for a, b in itertools.combinations(group, 2))
        permutations.append([group] if twin else itertools.permutations(group))
    def encode(permutation):
        return sum(1 << (j*(j-1)//2+i)
                   for j,v in enumerate(permutation) for i,u in enumerate(permutation[:j])
                   if rows[u] & (1 << v))
    return min(encode(sum((tuple(block) for block in perm), ())) for perm in itertools.product(*permutations))


def graph_orders(last):
    previous = [()]
    for n in range(1, last + 1):
        seen = {}
        for old in previous:
            for mask in range(1 << (n-1)):
                new = tuple(row | (((mask >> i) & 1) << (n-1)) for i,row in enumerate(old)) + (mask,)
                ident = canonical(new)
                if ident not in seen:
                    seen[ident] = new
        previous = list(seen.values())
        yield n, previous


def path_lengths(rows):
    """Maximum number of vertices in an exterior path between each ordered pair."""
    n = len(rows)
    lengths = [[0]*n for _ in rows]
    for root in range(n):
        def visit(v, used):
            lengths[root][v] = max(lengths[root][v], used.bit_count())
            for w in bits(rows[v] & ~used):
                visit(w, used | (1 << w))
        visit(root, 1 << root)
    return lengths


def positions(mask, distance):
    union = 0
    for length in range(1, distance+1):
        union |= (mask << length) | (mask >> length)
    return union


def near_path(rows, target):
    """A simple path in the mandatory-edge graph provides an actual contradiction."""
    @lru_cache(maxsize=None)
    def extend(v, used):
        if used.bit_count() >= target:
            return True
        return any(extend(w,used | (1 << w)) for w in bits(rows[v] & ~used))
    return any(extend(v,1 << v) for v in range(len(rows)))


def investigate(k, path_order, exterior, lengths, counters, examples, completion, saturated=False):
    p, b = path_order, len(exterior)
    n = p+b+1
    h = (k+1)//2
    degrees = [r.bit_count() for r in exterior]
    contacts = [0]*b
    choices = []
    for i, degree in enumerate(degrees):
        tail = max(lengths[i])
        locations = range(tail, p-tail)
        minimum = max(0,k-1-degree)
        maximum = min(len(locations), degree+1 if degree else k-1)
        family = []
        for cardinality in range(minimum,maximum+1):
            for seq in itertools.combinations(locations,cardinality):
                mask = sum(1 << v for v in seq)
                if not (mask & (mask << 1)):
                    family.append(mask)
        if not family:
            return
        choices.append(family)
    order = sorted(range(b),key=lambda i:len(choices[i]))
    def finish():
        # Each exterior component in H needs a contact with P.
        if any(not any(contacts[j] for j in range(b) if lengths[i][j]) for i in range(b)):
            return
        forced = [contacts[i].bit_count()+degrees[i] == k-1 for i in range(b)]
        cap = (1 << p)-1
        for i, mask in enumerate(contacts):
            two = positions(mask,1)
            for j in bits(exterior[i]):
                two |= contacts[j]
            witnesses = (two & ~mask & cap).bit_count()
            for j in range(b):
                if j!=i and not (exterior[i] & (1<<j)) and (
                    contacts[i] & contacts[j] or exterior[i] & exterior[j] or forced[i] and forced[j]):
                    witnesses += 1
            if witnesses>k:
                return
        counters['attachment patterns before path test'] += 1
        if saturated and b >= 3 and p == 2*b+1 and all(mask in (0,1<<b) for mask in contacts):
            # If the attachment starts a spanning exterior path, an edge between
            # the two b-vertex tails would give a longer H-path: the two possible
            # directions use b+2+i-j and b+2+j-i path vertices starting at the
            # middle contact. Thus its deletion with z leaves three b-vertex sides.
            rooted_spanning = any(mask and max(lengths[i]) == b for i,mask in enumerate(contacts))
            delta_floor = max(2, n-1-k-(k+1)**2//4)
            if rooted_spanning and b<=2*(delta_floor-2) and 2*b+4>=n-h-1:
                counters['excluded by three-component routing'] += 1
                return
        graph = [0]*n
        def edge(i,j):
            graph[i] |= 1<<j
            graph[j] |= 1<<i
        for i in range(1,p):
            edge(i-1,i)
        for i,row in enumerate(exterior):
            for j in bits(row):
                edge(p+i,p+j)
            for j in bits(contacts[i]):
                edge(p+i,j)
            if forced[i]:
                edge(p+i,n-1)
        if near_path(graph,n-h-1):
            counters['mandatory path meets gap bound'] += 1
            return
        if completion:
            from moderate_completion import exclude
            if exclude(graph,p,k,h):
                counters['excluded by completion constraints'] += 1
                return
        if saturated:
            # All path vertices other than t miss each of these exterior
            # vertices. Its predecessor spends its full even-distance budget
            # through t, and must be adjacent to the opposite path endpoint.
            # That chord opens a spanning path of P at t for the exterior.
            for t in range(1,p-1):
                if sum(mask == 1<<t for mask in contacts) >= k:
                    counters['excluded by saturated single contacts'] += 1
                    return
        counters['surviving patterns'] += 1
        if len(examples)<5:
            examples.append(dict(n=n,p=p,exterior=list(exterior),contacts=contacts.copy()))
    def assign(level):
        if level==b:
            finish()
            return
        i=order[level]
        for mask in choices[i]:
            if any(mask & positions(contacts[j],lengths[i][j]) for j in order[:level]):
                continue
            if any(exterior[i] & (1<<j) and (
                mask.bit_count()+contacts[j].bit_count()+degrees[j]>k+degrees[i] or
                mask.bit_count()+contacts[j].bit_count()+degrees[i]>k+degrees[j])
                for j in order[:level]):
                continue
            contacts[i]=mask
            assign(level+1)
    assign(0)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degrees',type=int,nargs='+')
    parser.add_argument('--complete',action='store_true',help='apply monotone exclusions and require zero surviving patterns')
    parser.add_argument('--orders',type=int,nargs=2,metavar=('MIN','MAX'),help='restrict to the given inclusive total orders, including beyond the moderate range')
    args=parser.parse_args()
    degrees=sorted(set(args.degrees))
    results={k: Counter() for k in degrees}
    examples={k: [] for k in degrees}
    windows = {k: tuple(args.orders) if args.orders else (2*k+3, 3*k+2) for k in degrees}
    for b, graphs in graph_orders(max(windows[k][1]-2*k for k in degrees)):
        print(f'exterior order {b}: {len(graphs)} isomorphism classes',flush=True)
        for k in degrees:
            h=(k+1)//2
            min_order,max_order=windows[k]
            if not h+1<=b<=max_order-2*k:
                continue
            for rows in graphs:
                ds=[x.bit_count() for x in rows]
                if ds.count(0)>1 or any(0<d<h-1 for d in ds):
                    continue
                lengths=path_lengths(rows)
                for p in range(max(2*k-1,min_order-b-1),max_order-b):
                    investigate(k,p,rows,lengths,results[k],examples[k],args.complete)
            print(k,b,dict(results[k]),flush=True)
    print(json.dumps({k:dict(counts=results[k],examples=examples[k]) for k in degrees},indent=2))
    if args.complete and any(results[k]['surviving patterns'] for k in degrees):
        raise SystemExit('unresolved completion patterns')


if __name__=='__main__':
    main()
