#!/usr/bin/env python3
"""Exclude unrestricted two-by-two completions for 1,625 prime base splits.

Use the first 58 primes as support. Take their greedy reciprocal-balance
split, all opposite-side one-for-one swaps, and all two-for-two swaps
involving only the largest 16 primes. The smallest new prime is bounded by
the total reciprocal deficit; the other three primes remain unrestricted.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations

from search_true_prime_two_pairs import balanced_base, primes_through, two_pair_candidates


def exchange(left, right, removed_left, removed_right):
    return (
        tuple(sorted((left - removed_left) | removed_right)),
        tuple(sorted((right - removed_right) | removed_left)),
    )


def split_family(base):
    left, right = map(set, balanced_base(base))
    yield 0, tuple(sorted(left)), tuple(sorted(right))
    for p in sorted(left):
        for q in sorted(right):
            yield 1, *exchange(left, right, {p}, {q})
    large = set(base[-16:])
    for left_pair in combinations(sorted(left & large), 2):
        for right_pair in combinations(sorted(right & large), 2):
            yield 2, *exchange(left, right, set(left_pair), set(right_pair))


def main():
    base = primes_through(271)
    assert len(base) == 58
    deficit = 2 - sum((Fraction(1, p) for p in base), Fraction(0))
    assert deficit > 0

    # A completion's full reciprocal mass is at least 2 by AM–GM.
    # If a is its globally smallest new prime, the four additions are
    # at most 4/a, so a <= 4/deficit. Orient its side as the left side.
    bound = 4 // deficit
    primes = primes_through(bound)
    totals = [Counter(), Counter(), Counter()]
    counts = Counter()
    family = list(split_family(base))
    assert len(set((left, right) for _, left, right in family)) == len(family)
    for swaps, left, right in family:
        counts[swaps] += 1
        for first, other in ((left, right), (right, left)):
            stats, hits = two_pair_candidates(first, other, primes, bound, globally_first=True)
            totals[swaps].update(stats)
            assert not hits, (first, other, hits)

    assert bound == 3_174 and counts == {0: 1, 1: 840, 2: 784}
    expected = ((782, 160, 299, 323),
                (656_880, 88_982, 293_222, 274_676),
                (613_088, 125_137, 255_791, 232_160))
    for stats, tally in zip(totals, expected):
        assert tuple(stats[k] for k in ("first", "nonpositive", "nonunit", "empty_interval")) == tally
        assert stats["right_candidates"] == stats["arithmetic_completions"] == 0
    print("Global smallest-closing-prime bound:", bound)
    print("Distinct splits by number of swaps:", dict(counts))
    for swaps, stats in enumerate(totals):
        print(f"{swaps} swaps:", dict(stats))
    print("Two-by-two prime completions: 0")


if __name__ == "__main__":
    main()
