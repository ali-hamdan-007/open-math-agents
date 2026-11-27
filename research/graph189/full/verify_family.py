"""Verify the explicit witness and its first few simultaneous true-twin extensions."""

from collections import deque
from itertools import combinations
from pathlib import Path
import re

WITNESS = Path("/workspace/scratch/6893ca6bed01/parallel/fresh-wow/search_189_order14.txt")
VERTEX_COUNT = 14
CLONED = {6, 8}
BASE_EDGES = {
    (int(a), int(b))
    for a, b in re.findall(r"\(e(\d+)_(\d+) true\)", WITNESS.read_text())
}


def bfs(adjacency, start, removed=None):
    distances = {start: 0}
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if neighbor != removed and neighbor not in distances:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    return distances


def check_twins(twins):
    roles = list(range(VERTEX_COUNT)) + [6, 8] * twins
    adjacency = [set() for _ in roles]
    for i, j in combinations(range(len(roles)), 2):
        left, right = sorted((roles[i], roles[j]))
        if (left, right) in BASE_EDGES or left == right in CLONED:
            adjacency[i].add(j)
            adjacency[j].add(i)
    distances = [bfs(adjacency, i) for i in range(len(roles))]
    degree = sorted(map(len, adjacency))
    s = degree[1]
    assert degree[0] == 2 and s == 5 + twins
    assert len(roles) == 2 * s + 4
    assert all(len(row) == len(roles) for row in distances)
    assert max(max(row.values()) for row in distances) == 3
    assert max(sum(d == 2 for d in row.values()) for row in distances) <= s
    assert all(
        len(bfs(adjacency, (i + 1) % len(roles), removed=i)) == len(roles) - 1
        for i in range(len(roles))
    )
    middle = {i for i, d in distances[0].items() if d == 2}
    remote = {i for i, d in distances[0].items() if d == 3}
    assert middle - adjacency[1] == {3} and middle - adjacency[2] == {4}
    assert {i for i in remote if adjacency[i] & middle not in ({3}, {4})} == {12, 13}
    return s


if __name__ == "__main__":
    print(f"Verified examples with second-smallest degree {check_twins(0)}–{check_twins(12)}.")
    for twin_count in range(1, 12):
        check_twins(twin_count)
