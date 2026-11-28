"""Replay the expansion test on small graphs and the sharpness constructions.

Run with Python 3 from this directory. The graph-type generator is shared
with the existing moderate-degree computation. All checks of the original
hypotheses and the expansion inequality are done here.
"""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "root"))
from moderate_exterior_search import bits, graph_orders


def distinct_layers(rows, root, allowed):
    frontier = 1 << root
    seen = frontier
    while frontier:
        yield frontier
        neighbors = 0
        for vertex in bits(frontier):
            neighbors |= rows[vertex]
        frontier = neighbors & allowed & ~seen
        seen |= frontier


def connected(rows, allowed):
    root = (allowed & -allowed).bit_length() - 1
    return sum(distinct_layers(rows, root, allowed)) == allowed


def even_caps(rows):
    all_vertices = (1 << len(rows)) - 1
    return tuple(
        sum(layer.bit_count() for distance, layer in
            enumerate(distinct_layers(rows, root, all_vertices))
            if distance > 0 and distance % 2 == 0)
        for root in range(len(rows))
    )


def small_connectivity(rows):
    order = len(rows)
    all_vertices = (1 << order) - 1
    for deleted_count in range(order - 1):
        for removed in combinations(range(order), deleted_count):
            allowed = all_vertices ^ sum(1 << vertex for vertex in removed)
            if not connected(rows, allowed):
                return deleted_count
    return order - 1


def exhaustive_small_graphs():
    totals = Counter()
    for order, graphs in graph_orders(7):
        if order < 2:
            continue
        all_vertices = (1 << order) - 1
        for rows in graphs:
            if not connected(rows, all_vertices):
                continue
            totals["connected"] += 1
            k = sorted(row.bit_count() for row in rows)[1]
            if max(even_caps(rows)) > k:
                continue
            totals["qualifying"] += 1
            connectivity = small_connectivity(rows)
            if connectivity < 2 or order < 2 * k + 3:
                continue
            totals["in_range"] += 1
            required_surplus = min(connectivity - 1, order - 2 * k - 2)
            for independent in range(1, 1 << order):
                neighbors = 0
                for v in bits(independent):
                    neighbors |= rows[v]
                if neighbors & independent:
                    continue
                assert neighbors.bit_count() >= independent.bit_count() + required_surplus
                totals["independent_sets"] += 1
    print("small exhaustive", dict(totals))


def sharpness_graph(k, connectivity):
    order = 3 * k + 1
    independent = tuple(range(k - connectivity + 1))
    separator = tuple(range(len(independent), len(independent) + k))
    gateways = tuple(range(len(independent) + k, len(independent) + k + connectivity))
    tail = tuple(range(len(independent) + k + connectivity, order))
    rows = [0] * order

    def add_edge(a, b):
        rows[a] |= 1 << b
        rows[b] |= 1 << a

    for a, b in combinations(separator, 2):
        add_edge(a, b)
    for a, b in combinations(gateways + tail, 2):
        add_edge(a, b)
    for a, b in product(separator, independent + gateways):
        add_edge(a, b)
    return rows, (independent, separator, gateways, tail)


def verify_sharpness(k, connectivity):
    rows, classes = sharpness_graph(k, connectivity)
    independent, separator, gateways, tail = classes
    order = len(rows)
    all_vertices = (1 << order) - 1
    assert sorted(row.bit_count() for row in rows)[1] == k
    even = even_caps(rows)
    for cls, expected in zip(classes, (k, k, len(independent), k)):
        assert all(even[v] == expected for v in cls)
    assert not connected(rows, all_vertices ^ sum(1 << v for v in gateways))

    # Each class consists of mutually exchangeable vertices. Every deletion
    # of the same size from each class has the same connectivity result.
    for counts in product(*(range(min(len(cls), connectivity - 1) + 1) for cls in classes)):
        if sum(counts) >= connectivity:
            continue
        deleted = sum(1 << v for cls, count in zip(classes, counts) for v in cls[:count])
        assert connected(rows, all_vertices ^ deleted)

    support = 0
    for v in independent:
        support |= rows[v]
    assert support == sum(1 << v for v in separator)
    surplus = len(separator) - len(independent)
    assert surplus == connectivity - 1

    witness = tuple(v for pair in zip(independent, separator) for v in pair)
    witness += separator[len(independent):] + gateways + tail
    assert len(witness) == order and set(witness) == set(range(order))
    assert all(rows[a] & (1 << b) for a, b in zip(witness, witness[1:]))
    print(f"sharpness n={order} k={k} connectivity={connectivity} "
          f"even_cap={max(even)} surplus={surplus} spanning_path=yes")


if __name__ == "__main__":
    exhaustive_small_graphs()
    for connectivity in (2, 3, 4):
        for k in (connectivity + 1, 26, 52):
            verify_sharpness(k, connectivity)
