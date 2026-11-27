"""Verify the local witnesses used in a056777_local_obstructions.md."""

from itertools import combinations
from math import isqrt

# prime: (p, q, roots, precision)
WITNESSES = {
    2: (23, 3, (137, 165, 427), 11),
    3: (7, 11, (112, 106, 467), 7),
    5: (3, 7, (2, 3, 4), 1),
    7: (5, 11, (1, 4, 5), 1),
    11: (1, 5, (6, 7, 8), 1),
    13: (1, 7, (3, 11, 12), 1),
    17: (1, 25, (4, 9, 10), 1),
    19: (3, 5, (1, 10, 17), 1),
    23: (1, 21, (8, 12, 14), 1),
    29: (1, 7, (4, 18, 20), 1),
    31: (1, 9, (8, 9, 30), 1),
    37: (1, 17, (15, 19, 31), 1),
    41: (1, 23, (3, 15, 19), 1),
    43: (1, 1, (21, 31, 38), 1),
    47: (1, 9, (25, 40, 45), 1),
    53: (1, 15, (6, 7, 12), 1),
    59: (1, 13, (4, 8, 10), 1),
    25841: (1, 5, (6012, 7223, 12616), 1),
}


def valuation(n, prime):
    assert n
    result = 0
    while n % prime == 0:
        result += 1
        n //= prime
    return result


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def verify():
    assert set(WITNESSES) == {n for n in range(2, 61) if is_prime(n)} | {25841}
    assert is_prime(25841)
    for prime, (p, q, roots, precision) in WITNESSES.items():
        assert p % prime and q % prime
        if prime == 2:
            assert p % 4 == 3 and q % 8 == 3
        if prime == 3:
            assert p % 3 != q % 3
        if prime == 5:
            assert p % 5 in (2, 3) and q % 5 == 2

        twice_sum = (p * p + p + 1) * (q + 1) + 2 * p**3
        assert twice_sum % 2 == 0
        root_sum = twice_sum // 2
        pair_sum = p**3 * (p + q - 1) + root_sum - 1
        product = p**4 * q + 12
        precision_at_root = {}
        for root in roots:
            assert root % prime
            assert (((root - root_sum) * root + pair_sum) * root - product) % prime**precision == 0
            derivative = (3 * root - 2 * root_sum) * root + pair_sum
            derivative_order = valuation(derivative, prime)
            assert precision > 2 * derivative_order
            precision_at_root[root] = precision - derivative_order

        for a, b in combinations(roots, 2):
            assert valuation(a - b, prime) < min(precision_at_root[a], precision_at_root[b])

    print(f"Verified Hensel witnesses at {len(WITNESSES)} exceptional primes.")


if __name__ == "__main__":
    verify()
