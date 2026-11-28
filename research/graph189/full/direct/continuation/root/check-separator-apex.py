"""Check the contact-path lemma by enumerating all labelled simple graphs of orders 3--6."""
from itertools import combinations


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def connected(adj, allowed):
    reached = 0
    frontier = allowed & -allowed
    while frontier:
        reached |= frontier
        extension = 0
        for x in vertices(frontier):
            extension |= adj[x]
        frontier = extension & allowed & ~reached
    return allowed == reached


def longest(adj, side, contacts):
    # ends[mask] records possible last vertices of a simple path which starts at a contact.
    ends = [0] * (1 << len(adj))
    for x in vertices(contacts):
        ends[1 << x] = 1 << x
    answer = 0
    for mask, last in enumerate(ends):
        if not last:
            continue
        answer = max(answer, mask.bit_count())
        for x in vertices(last):
            for y in vertices(adj[x] & side & ~mask):
                ends[mask | (1 << y)] |= 1 << y
    return answer


def verify(n):
    edges = list(combinations(range(n), 2))
    full = (1 << n) - 1
    side = full - 1
    cases = 0
    for code in range(1 << len(edges)):
        adj = [0] * n
        for bit in vertices(code):
            x, y = edges[bit]
            adj[x] |= 1 << y
            adj[y] |= 1 << x
        if min(x.bit_count() for x in adj) < 2:
            continue
        if not all(connected(adj, full ^ (1 << x)) for x in range(n)):
            continue
        degree = sorted(adj[x].bit_count() for x in range(1, n))[1]
        path_order = longest(adj, side, adj[0])
        assert path_order >= min(n-1, 2*degree-1), (n, code, path_order, degree)
        cases += 1
    return cases


if __name__ == "__main__":
    counts = [verify(n) for n in range(3, 7)]
    print("Labelled 2-connected graphs with apex fixed at vertex 0:", counts, "total", sum(counts))
