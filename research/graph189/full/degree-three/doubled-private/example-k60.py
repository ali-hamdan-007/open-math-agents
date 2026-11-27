"""Construct the k=60 doubled-private example and verify its graph distances."""
from collections import Counter, deque
from itertools import combinations


def add_edges(graph, pairs):
    for left, right in pairs:
        assert left != right
        graph.setdefault(left, set()).add(right)
        graph.setdefault(right, set()).add(left)


def star(graph, vertex, neighbors):
    add_edges(graph, ((vertex, other) for other in neighbors))


def construct():
    graph = {}
    anchors = ["A", "B", "C"]
    common = [f"w{i}" for i in range(56)]
    first = [f"x{i}" for i in range(60)]
    second = [f"y{i}" for i in range(60)]
    for clique in (anchors, common, first, second):
        add_edges(graph, combinations(clique, 2))
    star(graph, "z", anchors)
    for anchor in anchors:
        star(graph, anchor, common)
    star(graph, "A", ["p", "q"])
    star(graph, "B", ["b"])
    star(graph, "C", ["c"])

    star(graph, "q", common[:25])
    star(graph, "b", common[25:30])
    star(graph, "c", common[30:])
    star(graph, "p", common[1:25] + common[30:])
    star(graph, "p", first[:15])
    star(graph, "b", first[5:])
    star(graph, "q", second[:37])
    star(graph, "c", second[24:])
    star(graph, "t", common + ["p", "b"] + first[5:13])
    return graph, common, first, second


def distances(graph, source):
    levels = {source: 0}
    queue = deque([source])
    while queue:
        vertex = queue.popleft()
        for neighbor in graph[vertex]:
            if neighbor not in levels:
                levels[neighbor] = levels[vertex] + 1
                queue.append(neighbor)
    return levels


if __name__ == "__main__":
    graph, common, first, second = construct()
    distance = {v: distances(graph, v) for v in graph}
    assert all(len(row) == len(graph) for row in distance.values())
    middle = {v for v in graph if distance["z"][v] == 2}
    remote = {v for v in graph if distance["z"][v] == 3}
    anchors = graph["z"]
    assert middle == set(common + ["p", "q", "b", "c"])
    assert remote == set(first + second + ["t"])
    for group, support in ((common, anchors), (["p", "q"], {"A"}),
                           (["b"], {"B"}), (["c"], {"C"})):
        assert all(graph[v] & anchors == support for v in group)
    assert {v for v in remote if all(distance[a][v] == 2 for a in anchors)} == {"t"}
    degrees = sorted(map(len, graph.values()))
    assert (len(graph), degrees[:2], max(distance["z"].values())) == (185, [3, 60], 3)
    counts = {v: Counter(row.values()) for v, row in distance.items()}
    assert max(row[2] for row in counts.values()) == 60
    assert (counts["b"][2], counts["b"][4]) == (60, 60)
    path = ["q", *second, "c", "C", "z", "B", "b", *reversed(first), "p", "t", *common, "A"]
    assert len(path) == len(set(path)) == len(graph)
    assert all(b in graph[a] for a, b in zip(path, path[1:]))
    print("vertices, edges:", len(graph), sum(map(len, graph.values())) // 2)
    print("minimum, second degree, root eccentricity:", *degrees[:2], max(distance["z"].values()))
    print("maximum distance-two count:", max(row[2] for row in counts.values()))
    print("b distance-two and distance-four counts:", counts["b"][2], counts["b"][4])
    print("spanning path verified:", len(path), "vertices")
