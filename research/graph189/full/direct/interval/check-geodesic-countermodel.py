from collections import deque
from itertools import combinations, product

k, s, size = 3, 2, 7
gates = [('s', i) for i in range(s)]
cliques = [[('c', j, i) for i in range(size)] for j in range(s + 1)]
left = [('x', i) for i in range(k)]
right = [('y', i) for i in range(k)]
vertices = gates + sum(cliques, []) + left + right
neighbors = {v: set() for v in vertices}

def add(pairs):
    for u, v in pairs:
        neighbors[u].add(v)
        neighbors[v].add(u)

def distances(v, avoid=frozenset()):
    result, queue = {v: 0}, deque([v])
    while queue:
        p = queue.popleft()
        for q in neighbors[p] - avoid - result.keys():
            result[q] = result[p] + 1
            queue.append(q)
    return result

add(combinations(gates, 2))
for group in cliques:
    add(combinations(group, 2))
    add(product(gates, group))
add(product(left, right))
add(product(gates, [left[0], right[0]]))
assert min(map(len, neighbors.values())) == k
for v in vertices:
    other = next(iter(set(vertices) - {v}))
    assert len(distances(other, {v})) == len(vertices) - 1
x, y = left[1], right[1]
assert not (neighbors[x] & neighbors[y])
h = set(sum(cliques, []) + gates)
assert len(h) == s + (s+1)*size
# An upper bound for any path using the smaller component.
assert s+s*size+2*k < len(h)
checked = 0
for cl, cr in product(cliques, repeat=2):
    if cl is cr:
        continue
    middle = [g for g in cliques if g is not cl and g is not cr]
    for e, f in product(cl, cr):
        blocks = [[e] + [w for w in cl if w != e], *middle,
                  [w for w in cr if w != f] + [f]]
        path = []
        for i, block in enumerate(blocks):
            if i:
                path.append(gates[i-1])
            path.extend(block)
        assert set(path) == h and len(path) == len(h)
        assert all(v in neighbors[u] for u, v in zip(path, path[1:]))
        for v in (e, f):
            d = distances(v)
            assert d[x] == d[y] == 3
        route1, route2 = [e, gates[0], right[0], x], [f, gates[1], left[0], y]
        assert set(route1).isdisjoint(route2)
        for route in (route1, route2):
            assert all(v in neighbors[u] for u, v in zip(route, route[1:]))
        checked += 1
d = distances(cliques[0][0])
assert sum(dis == 2 for dis in d.values()) > k
print(f'Checked {len(vertices)} vertices and {checked} ordered compatible terminal pairs.')
