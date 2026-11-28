"""Screen two fixed clique-fiber templates against exact Graph 189 parity."""

from collections import deque
from itertools import combinations, product
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix


GATE = Path("/tmp/ali189-active.CE0Lol")


def active():
    return (GATE / "LIVE").exists() and not any(
        (GATE / flag).exists() for flag in ("PAUSE", "HALT")
    )


def make_template(bank_mode):
    adjacency = []
    minimum_weights = []
    fixed = []

    def vertex(min_weight=1, singleton=True):
        index = len(adjacency)
        adjacency.append(set())
        minimum_weights.append(min_weight)
        fixed.append(singleton)
        return index

    def edge(a, b):
        adjacency[a].add(b)
        adjacency[b].add(a)

    def join(part_a, part_b):
        for a, b in product(part_a, part_b):
            edge(a, b)

    def clique(vertices):
        for a, b in combinations(vertices, 2):
            edge(a, b)

    banks = [[[vertex() for _ in range(4)] for _ in range(2)] for _ in range(3)]
    clique([a for bank_set in banks for a in bank_set[0]])
    for lobe, (p0, p1) in enumerate(banks):
        clique(p1)
        if bank_mode == "complete":
            join(p0, p1)
        else:
            for i in range(4):
                edge(p0[i], p1[i])
                edge(p0[i], p1[(i + 1) % 4])
        for leaf in range(7):
            z = vertex()
            for layer, bank in enumerate((p0, p1)):
                port_a, port_b = vertex(2, False), vertex(2, False)
                remote = vertex(1, False)
                clique((z, port_a, port_b, remote))
                phase = (lobe + leaf + layer) % 4
                join((port_a,), (bank[phase], bank[(phase + 1) % 4]))
                join((port_b,), (bank[(phase + 2) % 4], bank[(phase + 3) % 4]))
    return adjacency, np.array(minimum_weights), np.array(fixed)


def distances(adjacency, source):
    distance = [-1] * len(adjacency)
    distance[source] = 0
    queue = deque([source])
    while queue:
        here = queue.popleft()
        for neighbor in adjacency[here]:
            if distance[neighbor] < 0:
                distance[neighbor] = distance[here] + 1
                queue.append(neighbor)
    return distance


def optimize(adjacency, minimum_weights, fixed, k):
    n = len(adjacency)
    defect_index = 2 * n
    # Variables are fiber weights, one optional low indicator per fiber, and
    # the maximum excess of a positive even count above the proposed k.
    matrix = lil_matrix((3 * n + 1, 2 * n + 1))
    lower = np.full(3 * n + 1, -np.inf)
    upper = np.full(3 * n + 1, np.inf)
    even_sets = []
    for v, neighbors in enumerate(adjacency):
        for u in neighbors | {v}:
            matrix[v, u] = 1
        matrix[v, n + v] = k
        lower[v] = k + 1
        # Any exceptional degree must be carried by a singleton fiber.
        matrix[n + v, v] = 1
        matrix[n + v, n + v] = k - 1
        upper[n + v] = k
        even_set = tuple(
            u for u, distance in enumerate(distances(adjacency, v))
            if distance > 0 and distance % 2 == 0
        )
        even_sets.append(even_set)
        for u in even_set:
            matrix[2 * n + v, u] = 1
        matrix[2 * n + v, defect_index] = -1
        upper[2 * n + v] = k
    matrix[3 * n, n:2 * n] = 1
    upper[3 * n] = 1
    # Every ordinary branch has size at most k in a qualifying graph, since
    # an opposite-branch vertex sees it at exact distance two.
    upper_weights = np.where(fixed, 1, k)
    domains = Bounds(
        np.r_[minimum_weights, np.zeros(n), 0],
        np.r_[upper_weights, np.ones(n), np.inf],
    )
    objective = np.zeros(2 * n + 1)
    objective[defect_index] = 1
    result = milp(
        objective,
        integrality=np.ones(2 * n + 1),
        bounds=domains,
        constraints=LinearConstraint(matrix.tocsr(), lower, upper),
        options={"time_limit": 8},
    )
    if result.x is None:
        return {"status": result.status, "message": result.message}
    values = np.rint(result.x).astype(int)
    weights = values[:n]
    degrees = [sum(weights[u] for u in neighbors | {v}) - 1
               for v, neighbors in enumerate(adjacency)]
    even_count = [sum(weights[u] for u in even_set) for even_set in even_sets]
    sorted_degrees = sorted(
        degree for v, degree in enumerate(degrees) for _ in range(weights[v])
    )
    assert sum(weight for weight, degree in zip(weights, degrees) if degree < k) <= 1
    assert max(even_count) - k == values[defect_index]
    return {
        "status": result.status,
        "minimum_defect": values[defect_index],
        "dual_bound": result.mip_dual_bound,
        "order": int(sum(weights)),
        "actual_k": sorted_degrees[1],
        "maximum_even_count": max(even_count),
    }


if __name__ == "__main__":
    for mode in ("complete", "cyclic"):
        adjacency, minimum_weights, fixed = make_template(mode)
        for k in (11, 12, 16, 24):
            if not active():
                raise SystemExit("lease paused")
            print(mode, k, optimize(adjacency, minimum_weights, fixed, k), flush=True)
