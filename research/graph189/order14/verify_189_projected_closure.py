"""Degree-eight certificate for the adjacent-anchor one-miss order-14 family."""
from collections import Counter
from itertools import combinations, combinations_with_replacement

def union(masks):
    result = 0
    for mask in masks:
        result |= mask
    return result

def selected(mask, rows):
    return union(row for index, row in enumerate(rows) if mask & (1 << index))

def middle_graphs():
    pairs = list(combinations(range(5), 2))
    for mask in range(1 << len(pairs)):
        rows = [0] * 5
        for index, (i, j) in enumerate(pairs):
            if mask & (1 << index):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        yield rows

def local_row(i, n, p, q):
    # p[r] and q[i] are the two directions of the W--R incidences.
    # n is the neighborhood of W vertex i within W.
    private = i < 2
    degree = 2 - private + n.bit_count() + q[i].bit_count()
    by_anchor = 0b11100 if private else 0b11111
    near_w = by_anchor | selected(q[i], p)
    second_w = near_w & ~(n | (1 << i))
    forced_r = sum(1 << r for r in range(6) if p[r].bit_count() < q[i].bit_count())
    second_r = (selected(n, q) | forced_r) & ~q[i]
    second_lower = 1 + private + second_w.bit_count() + second_r.bit_count()
    return degree, second_lower

def main():
    graphs = list(middle_graphs())
    histogram = Counter()
    pairs = 0
    for s, t in combinations_with_replacement(range(1, 32), 2):
        pairs += 1
        p = (1, 1, 2, 2, s, t)
        q = [sum(1 << r for r in range(6) if p[r] & (1 << i)) for i in range(5)]
        table = [[local_row(i, n, p, q) for n in range(32)] for i in range(5)]
        for graph in graphs:
            high = 0
            for i, n in enumerate(graph):
                degree, second_lower = table[i][n]
                if degree < 5 or second_lower > 5:
                    break
                high += degree >= 8
            else:
                histogram[high] += 1
    print(f'{pairs} remote-mask pairs x {len(graphs)} middle graphs')
    print('high middle vertices:', sorted(histogram.items()))
    assert (pairs, len(graphs)) == (496, 1024)
    assert histogram == {3: 13, 4: 21, 5: 6}

if __name__ == '__main__':
    main()
