"""Check the sharp diameter-three template bound with standard-library Python.

The theorem and argument are in diameter-three-templates.md. The first
three sets in a simple cover or the integer multiplicities in an exceptional
cover establish the inequality for every choice of positive clique sizes.
"""
from collections import deque
from itertools import combinations_with_replacement, permutations, product


def canonical_encoding(graph):
    """Refine colors, then minimize over all orders within each color."""
    colors = [sum(row) for row in graph]
    while True:
        descriptions = [
            (colors[i], tuple(sorted(colors[j] for j, edge in enumerate(row) if edge)))
            for i, row in enumerate(graph)
        ]
        rank = {description: i for i, description in enumerate(sorted(set(descriptions)))}
        refined = [rank[description] for description in descriptions]
        if refined == colors:
            break
        colors = refined

    classes = [
        [i for i, color in enumerate(colors) if color == rank]
        for rank in range(max(colors) + 1)
    ]
    minimum = None
    for ordered_classes in product(*(permutations(group) for group in classes)):
        order = sum(ordered_classes, ())
        code = bytes(graph[i][j] for offset, i in enumerate(order) for j in order[:offset])
        if minimum is None or code < minimum:
            minimum = code
    return minimum


def connected_templates(max_order):
    previous = [[[0]]]
    for n in range(2, max_order + 1):
        representatives = {}
        for graph in previous:
            for neighbors in range(1, 1 << (n - 1)):
                incidence = [(neighbors >> i) & 1 for i in range(n - 1)]
                expanded = [row + [incidence[i]] for i, row in enumerate(graph)]
                expanded.append(incidence + [0])
                representatives.setdefault(canonical_encoding(expanded), expanded)
        previous = list(representatives.values())
        yield n, previous


def diameter_three_neighborhoods(graph):
    """Return one (closed ball, positive even-distance set) pair per vertex."""
    n = len(graph)
    diameter = 0
    neighborhoods = []
    for start in range(n):
        distance = {start: 0}
        pending = deque([start])
        while pending:
            x = pending.popleft()
            for y, edge in enumerate(graph[x]):
                if edge and y not in distance:
                    distance[y] = distance[x] + 1
                    pending.append(y)
        if len(distance) != n:
            return None
        diameter = max(diameter, max(distance.values()))
        ball = sum(1 << i for i in range(n) if distance[i] <= 1)
        even = sum(1 << i for i in range(n) if distance[i] > 0 and distance[i] % 2 == 0)
        neighborhoods.append((ball, even))
    return neighborhoods if diameter == 3 else None


def simple_cover(neighborhoods):
    full = (1 << len(neighborhoods)) - 1
    even = [sphere for ball, sphere in neighborhoods]
    pairs = {a | b for a, b in combinations_with_replacement(even, 2)}
    if any((pair | sphere) == full for pair in pairs for sphere in even):
        return 1
    if all(any((pair | ball) == full for pair in pairs) for ball, sphere in neighborhoods):
        return 2
    return 0


# In each word the first n digits multiply the even sets, and the last
# digit multiplies the ball of the root. Words are indexed by that root.
EXCEPTIONAL_COVERS = {
    '110010001000010000011': (
        '32211001', '23120101', '21302011', '12030211',
        '10203121', '01021321', '00112231',
    ),
    '1101000100001000101100000110': (
        '311000102', '221120001', '212011011', '211120110',
        '110120111', '211120110', '211120110', '111021021',
    ),
    '1101000100001100000100000011': (
        '312102001', '230120101', '211112110', '211112110',
        '120030211', '202103011', '010021321', '000112231',
    ),
    '1100101100001001010100001010': (
        '212111001', '130100102', '103011002', '121201011',
        '330000003', '003003003', '303000003', '011202021',
    ),
    '1100100010111000001000000101': (
        '022113001', '031202101', '013022011', '020301211',
        '002031121', '022113001', '010210321', '001120231',
    ),
}


def verify_multiple_covers(neighborhoods, words):
    n = len(neighborhoods)
    assert len(words) == n
    for root, word in enumerate(words):
        assert len(word) == n + 1 and word.isdigit()
        multiplicities = [int(char) for char in word]
        ball_count = multiplicities[-1]
        total = sum(multiplicities)
        assert total <= 10 and 2 * total + ball_count <= 21
        for vertex in range(n):
            bit = 1 << vertex
            count = ball_count if neighborhoods[root][0] & bit else 0
            count += sum(
                multiplicities[i] for i, (_, even) in enumerate(neighborhoods) if even & bit
            )
            assert count >= 3


def verify_all():
    used = set()
    count = 0
    for n, representatives in connected_templates(8):
        totals = [0, 0, 0]
        for graph in representatives:
            neighborhoods = diameter_three_neighborhoods(graph)
            if neighborhoods is None:
                continue
            kind = simple_cover(neighborhoods)
            totals[kind] += 1
            if kind == 0:
                code = ''.join(str(graph[i][j]) for i in range(n) for j in range(i))
                verify_multiple_covers(neighborhoods, EXCEPTIONAL_COVERS[code])
                used.add(code)
        count += sum(totals)
        print(n, len(representatives), sum(totals), totals[1], totals[2], totals[0], flush=True)
    assert used == set(EXCEPTIONAL_COVERS)
    assert count == 6233
    print('Verified', count, 'diameter-three templates.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    verify_all()
