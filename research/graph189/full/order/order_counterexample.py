"""Verify unbounded violations of the proposed additive Graph 189 order bounds.

Usage: python order_counterexample.py [t]
The smallest reported counterexample to n <= 3k+2 is obtained at t=1.
The verifier constructs the graph and uses BFS, independently of the
closed formulas for the classwise degree and even-distance counts.
"""
from collections import deque
from sys import argv


def verify(t):
    if t < 0:
        raise ValueError("t must be a nonnegative integer")
    sizes = [1 + multiplier * t for multiplier in (2, 2, 3, 4, 4, 3, 2)]
    blocks = []
    n = 0
    for size in sizes:
        blocks.append(list(range(n, n + size)))
        n += size
    neighbors = [set() for vertex in range(n)]
    for i, block in enumerate(blocks):
        adj = set(blocks[i - 1] + block + blocks[(i + 1) % 7])
        for x in block:
            neighbors[x] = adj - {x}

    def distances(start, omit=None):
        result = {start: 0}
        queue = deque([start])
        while queue:
            x = queue.popleft()
            for y in neighbors[x]:
                if y != omit and y not in result:
                    result[y] = result[x] + 1
                    queue.append(y)
        return result

    # Consecutive labels form a Hamilton cycle, including the closing edge.
    assert all((x + 1) % n in neighbors[x] for x in range(n))
    assert all(len(distances((x + 1) % n, omit=x)) == n - 1 for x in range(n))
    degrees = [len(row) for row in neighbors]
    k = sorted(degrees)[1]
    even = []
    for x in range(n):
        ds = distances(x)
        assert len(ds) == n and max(ds.values()) == 3
        even.append(sum(d > 0 and d % 2 == 0 for d in ds.values()))
    class_degrees = [degrees[block[0]] for block in blocks]
    class_even = [even[block[0]] for block in blocks]
    for i, block in enumerate(blocks):
        assert all(degrees[x] == class_degrees[i] and even[x] == class_even[i]
                   for x in block)
    assert class_degrees == [2 + h*t for h in (6, 7, 9, 11, 11, 9, 7)]
    assert class_even == [2 + h*t for h in (6, 6, 6, 5, 5, 6, 6)]
    assert n == 20*t + 7 and k == 6*t + 2
    assert max(even) == k and n - 3*k == 2*t + 1
    print("class sizes:", sizes)
    print("class degrees:", class_degrees)
    print("positive even-distance counts:", class_even)
    print("order:", n, "second-smallest degree:", k, "excess over 3k:", n-3*k)


if __name__ == "__main__":
    verify(int(argv[1]) if len(argv) > 1 else 1)
