#!/usr/bin/env python3
"""Bounded test of the one-divisibility frame rule for base members 2..30."""
from math import gcd


def scan(limit=30):
    candidates = tuple(range(2, limit + 1))
    tested = integral = one = valid = 0
    examples = []

    def visit(first, left, right, m, md, n, nd):
        nonlocal tested, integral, one, valid
        if left and right:
            tested += 1
            delta = m * n - md * nd
            if delta > 0:
                p, r = divmod(m * nd + n * n, delta)
                q, s = divmod(md * n + m * m, delta)
                assert (r == 0) == (s == 0)
                if not r:
                    integral += 1
                    assert p * md + m == n * q and q * nd + n == m * p
                    if min(p, q) == 1:
                        one += 1
                        if len(examples) < 5:
                            examples.append((left, right, p, q))
                    if min(p, q) >= 2:
                        valid += 1
        for i in range(first, len(candidates)):
            a = candidates[i]
            if gcd(a, m * n) != 1:
                continue
            visit(i + 1, left + (a,), right, m * a, md * a + m, n, nd)
            if left:
                visit(i + 1, left, right + (a,), m, md, n * a, nd * a + n)

    # The least member belongs to the left side to quotient side-swap symmetry.
    visit(0, (), (), 1, 0, 1, 0)
    return tested, integral, one, valid, examples


if __name__ == "__main__":
    counts = scan()
    print("Frames, integral completions, containing 1, valid 1-free:", counts[:4])
    print("Examples of completions containing 1:", counts[4])
