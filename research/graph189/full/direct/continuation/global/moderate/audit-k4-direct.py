"""Independent direct-route check, with admissibility from explicit cut tests."""
import collections
import hashlib
import json
from pathlib import Path

catalog = Path(__file__).resolve().parents[2] / 'verify/moderate-certs/patterns-4.json'
records = json.loads(catalog.read_bytes())
assert len(records) == len({r['id'] for r in records}) == 30
kinds = collections.Counter()
losses = collections.Counter()
port_masks = 0
no_route_masks = 0
arm_max = 0


def connected_without(graph, cut):
    todo = [next(v for v in range(len(graph)) if v != cut)]
    seen = {cut, *todo}
    while todo:
        for w in graph[todo.pop()] - seen:
            seen.add(w)
            todo.append(w)
    return len(seen) == len(graph)


def exterior_route(g, available, start, finish):
    queue = [(start,)]
    while queue:
        path = queue.pop()
        if len(path) == len(available) + 1:
            if finish in g[path[-1]]:
                return path + (finish,)
            continue
        queue.extend(path + (v,) for v in (available & g[path[-1]]) - set(path))
    return None


for row in records:
    n, p, b = (row[k] for k in ('n', 'p', 'b'))
    assert n == p + b + 1
    z = n - 1
    P, E = set(range(p)), set(range(p, z))
    lower = [{w for w in range(n) if mask & (1 << w)} for mask in row['lower']]
    assert all((w in lower[v]) == (v in lower[w]) for w in range(n) for v in range(n))
    assert all(v + 1 in lower[v] for v in range(p-1))
    assert all(v not in lower[v] for v in range(n))
    c, = set.union(*(lower[v] & P for v in E))
    arm_sizes = (c, p-c-1)
    arm_max = max(arm_max, *arm_sizes)
    assert min(arm_sizes) > 0 and max(arm_sizes) <= 6
    forced = {v for v in E if len(lower[v]-{z}) < 4}
    assert all(len(lower[v]-{z}) >= 3 for v in E)
    assert lower[z] & E == forced
    edges = sum(len(lower[v] & E) for v in E)//2
    kind = (b, edges)
    kinds[kind] += 1
    for mask in range(1<<b):
        ports = {p+i for i in range(b) if mask & (1<<i)}
        if not forced <= ports:
            continue
        actual = [s.copy() for s in lower]
        for v in ports:
            actual[v].add(z)
            actual[z].add(v)
        upper = [s.copy() for s in actual]
        for v in P:
            upper[v].update((P | {z}) - {v})
            upper[z].add(v)
        if not all(connected_without(upper, cut) for cut in range(n)):
            no_route_masks += 1
            continue
        port_masks += 1
        route = exterior_route(actual, E, c, z)
        assert route and len(route) == b + 2
        for j in P - {c}:
            near, far = (0,p-1) if j<c else (p-1,0)
            def segment(a, end):
                step = 1 if a < end else -1
                return tuple(range(a,end+step,step))
            opposite = segment(far,c)
            first_inside = c - 1 if j<c else c + 1
            candidates = [opposite[:-1]+route+segment(j,end) for end in (near,first_inside)]
            witness = max(candidates,key=len)
            assert len(set(witness)) == len(witness)
            assert all(v in actual[u] or (u,v)==(z,j) for u,v in zip(witness,witness[1:]))
            losses[n-len(witness)] += 1
            assert len(witness) >= n-2
print('catalog SHA-256',hashlib.sha256(catalog.read_bytes()).hexdigest())
print('row counts by (outside order,edge count)',dict(sorted(kinds.items())))
print('largest arm',arm_max,'viable exterior z-masks',port_masks,'blocked masks after degree floor',no_route_masks)
print('route checks by omitted vertex count',dict(sorted(losses.items())))
print('total routes',sum(losses.values()))
