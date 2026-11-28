"""Verify a two-cycle factor with no direct two-edge merge."""

from itertools import product
from replay import connected, even_caps, sharpness_graph


def cycle_edges(cycle):
    return tuple(edge(a, b) for a, b in zip(cycle, cycle[1:] + cycle[:1]))


def edge(a, b):
    return tuple(sorted((a, b)))


def factor_rows(order, edges):
    rows = [0] * order
    for a, b in edges:
        rows[a] |= 1 << b
        rows[b] |= 1 << a
    return rows


def verify(k, connectivity):
    rows, classes = sharpness_graph(k, connectivity)
    independent, separator, gateways, tail = classes
    assert max(even_caps(rows)) == sorted(row.bit_count() for row in rows)[1] == k

    order = len(rows)
    apex = order
    rows = [row | (1 << apex) for row in rows] + [(1 << order) - 1]

    first_gap, rest_gaps = separator[:connectivity + 1], separator[connectivity + 1:]
    path = (independent[0],) + first_gap + (independent[1],)
    path += tuple(vertex for pair in zip(rest_gaps, independent[2:]) for vertex in pair)
    inner_cycle = (apex,) + path
    outer_cycle = tuple(vertex for pair in zip(gateways, tail) for vertex in pair)
    outer_cycle += tail[connectivity:]

    first, second = cycle_edges(inner_cycle), cycle_edges(outer_cycle)
    all_edges = set(first + second)
    assert all(rows[a] & (1 << b) for a, b in all_edges)
    assert sorted(inner_cycle + outer_cycle) == list(range(order + 1))

    for (a, b), (c, d) in product(first, second):
        assert not (rows[a] & (1 << c) and rows[b] & (1 << d))
        assert not (rows[a] & (1 << d) and rows[b] & (1 << c))

    q1, q2 = gateways[:2]
    t1, t2 = tail[:2]
    s1, s2 = first_gap[:2]
    asserted_outer_edge = edge(q1, q2)
    moves = (
        ((edge(q1, t1), edge(q2, t2)), (asserted_outer_edge, edge(t1, t2))),
        ((asserted_outer_edge, edge(s1, s2)), (edge(q1, s1), edge(q2, s2))),
    )
    for removed, inserted in moves:
        assert all(e in all_edges for e in removed)
        assert all(rows[a] & (1 << b) for a, b in inserted)
        all_edges.difference_update(removed)
        all_edges.update(inserted)
        assert all(row.bit_count() == 2 for row in factor_rows(order + 1, all_edges))
    assert connected(factor_rows(order + 1, all_edges), (1 << (order + 1)) - 1)

    print(f"k={k} connectivity={connectivity} n={order} "
          f"crossing_switches_tested={len(first) * len(second) * 2} "
          "direct_merges=0 two_switch_cycle=yes")


if __name__ == "__main__":
    for connectivity in (2, 3, 4):
        for k in (11, 26, 52):
            verify(k, connectivity)
