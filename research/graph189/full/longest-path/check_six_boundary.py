"""Endpoint audit on all labeled six-vertex graphs, using all spanning orders."""
from itertools import combinations, permutations

vertices = range(6)
edge_bit = {edge: 1 << j for j, edge in enumerate(combinations(vertices, 2))}
stars = [sum(bit for edge, bit in edge_bit.items() if v in edge) for v in vertices]
paths = [
    (sum(edge_bit[tuple(sorted(edge))] for edge in zip(p, p[1:])), p[0], p[-1])
    for p in permutations(vertices) if p[0] < p[-1]
]
eligible = non_hamilton_connected = failed_candidates = checked_contacts = 0
for graph in range(1 << len(edge_bit)):
    degrees = [(graph & star).bit_count() for star in stars]
    if min(degrees) < 3:
        continue
    eligible += 1
    ends = [0] * 6
    for path, a, b in paths:
        if graph & path == path:
            ends[a] |= 1 << b
            ends[b] |= 1 << a
    if all(endpoints.bit_count() == 5 for endpoints in ends):
        continue
    non_hamilton_connected += 1
    low = [v for v in vertices if degrees[v] == 3]
    assert len(low) >= 3
    assert all(endpoints.bit_count() >= 3 for endpoints in ends)
    for contacts in range(1 << 6):
        if contacts.bit_count() >= 3:
            checked_contacts += 1
            if all(ends[v] & contacts == 0 for v in low):
                failed_candidates += 1
print(eligible, non_hamilton_connected, checked_contacts, failed_candidates)
assert failed_candidates == 0
