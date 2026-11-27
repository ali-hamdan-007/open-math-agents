"""Verify the mod-59 fixed-size obstruction using only integer arithmetic."""

from itertools import combinations_with_replacement
from math import isqrt, prod


MODULUS = 59
CUTOFF = 77_933
EXCLUDED_RECIPROCALS = {1, 6, 15, 19, 25, 27, 31, 41, 48, 51, 53, 58}
EXTRA = {78_241, 78_487}
SCALE = 10**12
QUADRATIC_WITNESS = {3, 5, 61}
SIMULTANEOUS_WITNESS = {3, 5, 7, 29, 109}


def inverse(value):
    return pow(value, -1, MODULUS)


def prime_set(limit):
    sieve = bytearray(b"\1") * (limit + 1)
    sieve[0] = sieve[1] = 0
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((limit - start) // prime + 1)
    return {prime for prime in range(2, limit + 1) if sieve[prime]}


def product_and_reciprocal_sum(values):
    return prod(values) % MODULUS, sum(map(inverse, values)) % MODULUS


def main():
    primes = prime_set(max(EXTRA))
    assert EXTRA <= primes and all(prime > CUTOFF for prime in EXTRA)
    support = {
        prime
        for prime in primes - {2, MODULUS}
        if prime <= CUTOFF and inverse(prime) not in EXCLUDED_RECIPROCALS
    } | EXTRA
    assert len(support) == 6094
    assert {inverse(prime) for prime in support} == (
        set(range(1, MODULUS)) - EXCLUDED_RECIPROCALS
    )
    assert min(primes - support - {2, MODULUS}) == 167
    mass_lower_bound = sum(SCALE // prime for prime in support)
    assert mass_lower_bound == 2_000_102_412_336 > 2 * SCALE

    n, total_sum = product_and_reciprocal_sum(support)
    c = n * total_sum % MODULUS
    assert (n, c) == (15, 30)
    roots = {
        x
        for x in range(1, MODULUS)
        if (x * x - c * x + n * n) % MODULUS == 0
    }
    assert roots == {15}

    assert QUADRATIC_WITNESS <= support
    a, u = product_and_reciprocal_sum(QUADRATIC_WITNESS)
    b, _ = product_and_reciprocal_sum(support - QUADRATIC_WITNESS)
    assert (a, b, u) == (30, 30, 3)
    assert (a * a + b * b) % MODULUS == c

    triple_counts = {2: 0, 57: 0}
    for triple in combinations_with_replacement(range(1, MODULUS), 3):
        triple_product = prod(triple) % MODULUS
        if sum(triple) % MODULUS == 1 and triple_product in triple_counts:
            triple_counts[triple_product] += 1
            assert EXCLUDED_RECIPROCALS.intersection(triple)
    assert triple_counts == {2: 7, 57: 9}

    assert SIMULTANEOUS_WITNESS <= support
    a, u = product_and_reciprocal_sum(SIMULTANEOUS_WITNESS)
    b, v = product_and_reciprocal_sum(support - SIMULTANEOUS_WITNESS)
    assert pow(a, 2, MODULUS) == 15 and (u, v) == (1, 1)
    assert a * u % MODULUS == b and b * v % MODULUS == a
    print("Verified a quadratic witness at size 3 and both swaps at size 5.")
    print("All 16 modular triple candidates for both swaps are excluded.")


if __name__ == "__main__":
    main()
