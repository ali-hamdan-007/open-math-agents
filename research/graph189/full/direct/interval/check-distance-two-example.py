from collections import Counter, deque
from itertools import combinations

intervals = {'a': (5, 6), 'z': (5.5, 5.5)}
for direction in (-1, 1):
    for offset, size in enumerate((2, 2, 1, 3, 2), 1):
        left = 5 + direction * offset
        for twin in range(size):
            intervals[direction, offset, twin] = (left, left + 1)
neighbors = {vertex: set() for vertex in intervals}
for x, y in combinations(intervals, 2):
    ax, bx = intervals[x]
    ay, by = intervals[y]
    if max(ax, ay) <= min(bx, by):
        neighbors[x].add(y)
        neighbors[y].add(x)

def distances(start, removed=frozenset()):
    queue = deque([start])
    distance = {start: 0}
    while queue:
        current = queue.popleft()
        for neighbor in neighbors[current] - removed - distance.keys():
            distance[neighbor] = distance[current] + 1
            queue.append(neighbor)
    return distance

expected = [(5, 4, 10), (1, 4, 10), (4, 4, 9), (4, 4, 9), (5, 4, 10), (5, 2, 8), (4, 1, 9)]
for vertex in intervals:
    index = 0 if vertex == 'a' else 1 if vertex == 'z' else vertex[1] + 1
    counts = Counter(distances(vertex).values())
    assert (counts[1], counts[2], sum(n for d, n in counts.items() if d and not d % 2)) == expected[index]
remaining = set(intervals) - {'a'}
sizes = []
while remaining:
    component = distances(next(iter(remaining)), {'a'})
    remaining.difference_update(component)
    sizes.append(len(component))
assert sorted(sizes) == [1, 10, 10]
print(f'All {len(intervals)} distance rows verified; components after deletion have sizes {sorted(sizes)}.')
