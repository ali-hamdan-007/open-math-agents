from collections import Counter, deque
from itertools import combinations

vertices = ["z", "A", "B", "C", "p", "q", "b", "c", "t"]
w = [f"w{i}" for i in range(56)]
x = [f"x{i}" for i in range(60)]
y = [f"y{i}" for i in range(60)]
graph = {v: set() for v in vertices + w + x + y}


def attach(v, neighbors):
    for u in neighbors:
        graph[v].add(u)
        graph[u].add(v)


for group in (["A", "B", "C"], w, x, y):
    for v, u in combinations(group, 2):
        attach(v, [u])

attach("z", ["A", "B", "C"])
attach("A", ["p", "q"] + w)
attach("B", ["b"] + w)
attach("C", ["c"] + w)
attach("p", w[1:25] + w[30:] + x[:15] + ["t"])
attach("q", w[:25] + y[:37])
attach("b", w[25:30] + x[5:] + ["t"])
attach("c", w[30:] + y[24:])
attach("t", w + x[5:13])


def bfs(source):
    distances = {source: 0}
    queue = deque([source])
    while queue:
        v = queue.popleft()
        for u in graph[v] - distances.keys():
            distances[u] = distances[v] + 1
            queue.append(u)
    return distances


dist = {v: bfs(v) for v in graph}
stats = {v: Counter(d.values()) for v, d in dist.items()}
assert len(graph) == 185
assert all(len(d) == 185 for d in dist.values())
assert max(dist["z"].values()) == 3
assert max(max(d.values()) for d in dist.values()) == 5
assert min(len(graph[v]) for v in graph if v != "z") == 60
assert max(hist[2] for hist in stats.values()) == 60
assert stats["b"][2] == 60 and stats["b"][4] == 60
visibility = Counter("".join(a for a in "ABC" if dist[a][v] == 2)
                     for v in graph if dist["z"][v] == 3)
assert visibility == {"A": 29, "B": 45, "C": 23, "AB": 10, "AC": 13, "ABC": 1}
path = [v for v in x if v != "x5"] + ["x5", "t", "b", "B", "z", "A", "p"]
path += w[1:] + ["w0", "q"] + y + ["c", "C"]
assert len(path) == len(set(path)) == len(graph)
assert set(path) == graph.keys()
assert all(u in graph[v] for u, v in zip(path, path[1:]))
print(len(graph), stats["z"], stats["b"], visibility)
print("All 185 BFS searches and the spanning path verified.")
