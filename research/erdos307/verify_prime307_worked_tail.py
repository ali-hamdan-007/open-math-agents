#!/usr/bin/env python3
"""Exact nonresidue certificate for the fixed partial support of #307."""

from math import prod
from search_true_prime_two_pairs import is_prime, primes_through


def jacobi(n, m):
    assert m > 0 and m % 2
    n %= m
    sign = 1
    while n:
        while n % 2 == 0:
            n //= 2
            if m % 8 in (3, 5):
                sign = -sign
        n, m = m, n
        if n % 4 == m % 4 == 3:
            sign = -sign
        n %= m
    return sign if m == 1 else 0


def main():
    support = primes_through(271) + [283, 307, 311]
    assert len(support) == len(set(support)) == 61
    assert all(is_prime(p) for p in support)
    d = prod(support)
    n = sum(d // p for p in support)
    plus, minus = n + 2 * d, n - 2 * d
    p = 2_424_113
    assert is_prime(p)
    assert minus % p == 0
    assert d % p == 132_834
    assert pow(d, (p - 1) // 2, p) == p - 1
    assert jacobi(d, plus) == jacobi(d, minus) == 1
    print("Aggregate Jacobi signs:", jacobi(d, plus), jacobi(d, minus))
    print("Prime divisor of the minus coefficient:", p)
    print("Required square residue:", d % p)
    print("Euler-test residue:", pow(d, (p - 1) // 2, p))
    print("The global minus-square has no solution for any final prime.")


if __name__ == "__main__":
    main()
