#!/usr/bin/env python3
"""Exact mass bounds once a new prime is known to exceed 100,000."""

from fractions import Fraction
from search_true_prime_two_pairs import primes_through


def main():
    primes = primes_through(100_003)
    base = primes[:58]
    assert base[-1] == 271 and primes[-1] == 100_003
    deficit = 2 - sum((Fraction(1, p) for p in base), Fraction(0))
    assert deficit > 0
    for count, last_allowed, first_excluded in ((3, 1597, 1601), (4, 2389, 2393)):
        boundary = primes.index(first_excluded)
        assert primes[boundary - 1] == last_allowed
        largest_other_masses = sum(
            (Fraction(1, p) for p in primes[boundary : boundary + count - 1]),
            Fraction(1, 100_003),
        )
        # Every choice of distinct new primes with this minimum or larger
        # has no more mass. At least one of them must exceed 100,000.
        assert largest_other_masses < deficit
        print(f"With at most {count} new primes, the smallest is at most {last_allowed}.")


if __name__ == "__main__":
    main()
