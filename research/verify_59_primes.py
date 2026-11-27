#!/usr/bin/env python3
"""Exhaust the 59-element prime sets with reciprocal sum at least two.

For a prime set T write D = product(T) and N = sum(D/p for p in T).
If T is a disjoint union P ∪ Q with numer(P) = denom(Q) and vice versa,
then N = denom(P)^2 + denom(Q)^2 and D = denom(P)*denom(Q).
Consequently N^2 - 4*D^2 must be an integer square.
"""

from bisect import bisect_right
from math import isqrt, prod


def primes_below(limit):
    return [
        n
        for n in range(2, limit)
        if all(n % d for d in range(2, isqrt(n) + 1))
    ]


def verify():
    # Any 58 distinct primes have reciprocal sum at most the sum for the
    # smallest 58. For a 59-set containing p >= 1000, add at most 1/1000.
    # This proves that the bounded prime list contains every candidate.
    primes = primes_below(1000)
    common = prod(primes)
    weights = [common // p for p in primes]
    target = 2 * common
    assert 1000 * sum(weights[:58]) + common < 1000 * target

    # For a fixed omitted prime p among the smallest 59, the largest possible
    # reciprocal sum is attained by replacing p with the 60th smallest prime.
    mandatory = bisect_right(primes, 167)
    best_59 = sum(weights[:59])
    assert best_59 - weights[mandatory - 1] + weights[59] < target

    prefix = [0]
    for weight in weights:
        prefix.append(prefix[-1] + weight)

    kept = max_prime = nodes = 0
    square_cases = []

    def visit(start, remaining, weight, chosen):
        nonlocal kept, max_prime, nodes
        nodes += 1
        if remaining == 0:
            assert weight >= target
            kept += 1
            max_prime = max(max_prime, chosen[-1])
            denominator = prod(chosen)
            numerator = sum(denominator // p for p in chosen)
            discriminant = numerator**2 - 4 * denominator**2
            assert discriminant >= 0
            if isqrt(discriminant) ** 2 == discriminant:
                square_cases.append(tuple(chosen))
            return

        for i in range(start, len(primes) - remaining + 1):
            # Given that index i is chosen next, the following remaining-1
            # weights can only be smaller than the consecutive largest ones.
            # This upper bound decreases as i increases, since weights decrease.
            upper = weight + prefix[i + remaining] - prefix[i]
            if upper < target:
                break
            chosen.append(primes[i])
            visit(i + 1, remaining - 1, weight + weights[i], chosen)
            chosen.pop()

    visit(mandatory, 59 - mandatory, prefix[mandatory], primes[:mandatory])
    assert (mandatory, nodes, kept, max_prime) == (39, 59755, 49961, 787)
    assert not square_cases, square_cases
    print(f"Forced primes: {mandatory}")
    print(f"Search nodes: {nodes}")
    print(f"Candidate sets: {kept}")
    print(f"Largest candidate prime: {max_prime}")
    print(f"Square discriminants: {len(square_cases)}")


if __name__ == "__main__":
    verify()
