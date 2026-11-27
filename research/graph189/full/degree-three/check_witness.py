"""Independently check the 13-vertex degree-three order witness."""
from collections import deque

edges = [
    (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 7), (2, 4),
    (2, 5), (3, 6), (3, 7), (4, 5), (4, 10), (4, 12), (5, 10),
    (5, 12), (6, 7), (6, 8), (6, 9), (6, 11), (7, 8), (8, 9),
    (8, 11), (9, 10), (9, 11), (9, 12), (10, 11), (11, 12),
]
path = [0, 1, 2, 4, 10, 9, 8, 7, 3, 6, 11, 12, 5]
graph = [set() for _ in range(13)]
for u, v in edges:
    assert u != v and v not in graph[u]
    graph[u].add(v)
    graph[v].add(u)

degrees = [len(neighbors) for neighbors in graph]
assert sorted(degrees)[:2] == [3, 4]

for start in range(13):
    distances = {start: 0}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in distances:
                distances[v] = distances[u] + 1
                queue.append(v)
    assert len(distances) == 13 and max(distances.values()) == 3
    assert sum(d > 0 and d % 2 == 0 for d in distances.values()) == 4

assert sorted(path) == list(range(13))
assert all(v in graph[u] for u, v in zip(path, path[1:]))
print("Verified n=13, minimum degree 3, second-smallest degree 4, "
      "every eccentricity 3, every even-distance count 4, and a Hamilton path.")
