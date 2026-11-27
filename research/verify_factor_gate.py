#!/usr/bin/env python3
"""Exact fixed-product obstruction for left base {2,3,5}."""

from fractions import Fraction
from math import gcd, isqrt, prod


def is_prime(n):
    return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n) + 1))


def verify():
    left = (2, 3, 5)
    right_primes = (7, 11, 13, 17, 19, 23, 31)
    m, n = prod(left), prod(right_primes)
    u = sum(m // a for a in left)
    v_max = sum(n // b for b in right_primes)
    assert all(is_prime(b) for b in right_primes)
    assert len(set(right_primes)) == len(right_primes) and gcd(m, n) == 1

    # For a pairwise coprime grouping with product n, each right atom is a
    # product of distinct members of right_primes. Splitting atoms only
    # increases the reciprocal sum, so v_max is the maximum right cofactor.
    d_min = m * n - u * v_max
    k = u * n + m**2
    assert is_prime(k)
    assert d_min > 1

    # Even the ungrouped base passes the determinant and size tests. It fails
    # integrality, and the same obstruction rules out all coarser groupings.
    p = Fraction(m * v_max + n**2, d_min)
    q = Fraction(k, d_min)
    assert min(p, q) >= 2
    assert p.denominator != 1 and q.denominator != 1

    # Positive d divides the prime k, so d is 1 or k. The lower bound d_min
    # excludes 1, and d=k forces q=1.
    print("Fixed right product:", n)
    print("Prime completion numerator:", k)
    print("Determinant lower bound across all coprime groupings:", d_min)
    print("Ungrouped rational completions:", p, q)
    print("Viable coprime groupings: 0")


if __name__ == "__main__":
    verify()
