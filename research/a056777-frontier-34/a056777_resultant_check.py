"""Bounded exact check of the odd squarefree-three versus p**4*q branch."""

import argparse
from bisect import bisect_left
from math import isqrt

# Coefficients in descending degree order of the checked resultant polynomial P.
P_COEFFICIENTS = (
    1, 2, -1, -2, 1, -13, -32, -29, 2, 29, 72, 234,
    438, 492, 432, 216, 72,
)


def primes_through(limit):
    prime = bytearray(b"\x01") * (limit + 1)
    prime[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if prime[divisor]:
            start = divisor * divisor
            prime[start::divisor] = b"\x00" * ((limit - start) // divisor + 1)
    return [value for value, flag in enumerate(prime) if flag], prime


def double_resultant_polynomial(p):
    value = 0
    for coefficient in P_COEFFICIENTS:
        value = value * p + coefficient
    return 2 * value


def is_prime(value, primes, flags):
    if 0 <= value < len(flags):
        return bool(flags[value])
    if value < 2:
        return False
    root = isqrt(value)
    for prime in primes:
        if prime > root:
            return True
        if value % prime == 0:
            return False
    # This extension handles the larger cubic roots without assumptions about
    # the length of the sieve.
    for divisor in range(primes[-1] + 2, root + 1, 2):
        if value % divisor == 0:
            return False
    return True


def complete_triple(p, q, root, primes, flags):
    twice_sum = (p * p + p + 1) * (q + 1) + 2 * p**3
    pair_sum = p**3 * (p + q - 1) + twice_sum // 2 - 1
    remaining_sum = twice_sum // 2 - root
    remaining_product, remainder = divmod(p**4 * q + 12, root)
    if twice_sum % 2 or remainder:
        return None
    if remaining_product + root * remaining_sum != pair_sum:
        return None
    discriminant = remaining_sum**2 - 4 * remaining_product
    if discriminant < 0:
        return None
    delta = isqrt(discriminant)
    if delta**2 != discriminant or (remaining_sum - delta) % 2:
        return None
    a = (remaining_sum - delta) // 2
    b = (remaining_sum + delta) // 2
    if min(a, b) <= q or len({root, a, b}) != 3:
        return None
    if not (is_prime(a, primes, flags) and is_prime(b, primes, flags)):
        return None
    return tuple(sorted((root, a, b)))


def check(limit):
    primes, flags = primes_through(limit)
    p_count = root_count = divisor_count = q_count = 0
    solutions = set()
    first_root = bisect_left(primes, 13)
    for p in primes[bisect_left(primes, 23):]:
        if p % 4 != 3 or p % 5 not in (2, 3):
            continue
        p_count += 1
        h = p * p + p + 1
        p3, p4 = p**3, p**4
        target = double_resultant_polynomial(p)
        # The checked inequalities imply q < x < p and p**2 < q**3 < x**3.
        for x in primes[first_root:bisect_left(primes, p)]:
            if x**3 <= p * p:
                continue
            root_count += 1
            t = (h * x - (2 * p3 + h)) * x + 2 * p4
            assert t > 0
            if target % t:
                continue
            divisor_count += 1
            b = ((2 * x - h - 2 * p3) * x + 2 * p4 + h - 2) * x - 24
            q, remainder = divmod(b, t)
            if remainder or not 11 <= q < x or not flags[q]:
                continue
            if 70 * q >= 29 * p or p * p >= q**3 or p % 3 == q % 3:
                continue
            if q % 8 != 3 or q % 5 != 2:
                continue
            q_count += 1
            triple = complete_triple(p, q, x, primes, flags)
            if triple:
                solutions.add((p, q, triple))
    return {
        "p_limit": limit,
        "p_candidates": p_count,
        "short_root_candidates": root_count,
        "resultant_divisors": divisor_count,
        "reconstructed_q_candidates": q_count,
        "solutions": sorted(solutions),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p-limit", type=int, default=10000)
    args = parser.parse_args()
    if args.p_limit < 23:
        parser.error("--p-limit must be at least 23")
    print(check(args.p_limit))
