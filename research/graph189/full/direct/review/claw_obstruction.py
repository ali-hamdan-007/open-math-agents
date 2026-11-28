"""Rebuild the induced-claw obstruction and check it by shortest paths."""
from collections import deque
from itertools import combinations


def check(weights, damaged, center_part, third_part):
    parts = []
    order = 0
    for size in weights:
        parts.append(list(range(order, order + size)))
        order += size
    graph = [set() for _ in range(order)]
    for i, part in enumerate(parts):
        edges = list(combinations(part, 2))
        edges.extend((u, v) for u in part for v in parts[(i + 1) % 7])
        for u, v in edges:
            graph[u].add(v)
            graph[v].add(u)
    x, y = parts[damaged][:2]
    graph[x].remove(y)
    graph[y].remove(x)
    center, z = parts[center_part][0], parts[third_part][0]
    assert set([x, y, z]) <= graph[center]
    assert all(v not in graph[u] for u, v in combinations([x, y, z], 2))
    degree = [len(neighbors) for neighbors in graph]
    k = sorted(degree)[1]
    max_even = 0
    for root in range(order):
        distances = {root: 0}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in distances:
                    distances[v] = distances[u] + 1
                    queue.append(v)
        assert len(distances) == order
        max_even = max(max_even, sum(0 < d and d % 2 == 0 for d in distances.values()))
    max_sum = max(degree[u] + degree[v] for u, v in combinations(range(order), 2) if v not in graph[u])
    leaf_sum = max(degree[u] + degree[v] for u, v in combinations([x, y, z], 2))
    # Swap the second and third vertices in the imperfect clique to bypass xy.
    order_by_part = [part[:] for part in parts]
    part = order_by_part[damaged]
    part[1], part[2] = part[2], part[1]
    cycle = [v for part in order_by_part for v in part]
    assert len(set(cycle)) == order
    assert all(v in graph[u] for u, v in zip(cycle, cycle[1:] + cycle[:1]))
    assert max_even <= k and order > 3 * k + 2 and max_sum < order - 1
    return order, k, max_even, leaf_sum, max_sum


if __name__ == '__main__':
    print("order k maximum_even maximum_leaf_pair maximum_nonedge")
    small = check((3, 3, 4, 5, 5, 4, 3), 3, 2, 1)
    assert small == (27, 8, 8, 24, 24)
    print(*small)
    coeffs = (2, 2, 3, 4, 4, 3, 2)
    for t in range(2, 13):
        row = check(tuple(2 + t * c for c in coeffs), 1, 0, 6)
        assert row == (20*t+14, 6*t+5, 6*t+5, 14*t+9, 20*t+10)
        print(*row)
