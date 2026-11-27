#!/usr/bin/env python3
"""Exact two-by-two prime frame search for an independently chosen fixed base.

All four closing primes are unrestricted. First a uniform interval excludes
the entire large-first-prime tail. A congruence and a narrower interval then
exhaust the finitely many remaining first primes. All arithmetic is exact.
"""

from fractions import Fraction
from math import gcd, isqrt, prod


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\0" * ((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def balanced_base(primes):
    sides = ([], [])
    masses = [Fraction(0), Fraction(0)]
    for p in primes[:58]:
        side = int(masses[1] < masses[0])
        sides[side].append(p)
        masses[side] += Fraction(1, p)
    return sides


def two_pair_candidates(left, right, primes, first_bound, *, globally_first=False):
    m, n = prod(left), prod(right)
    md = sum(m // p for p in left)
    v = sum(n // q for q in right)
    base = set(left) | set(right)
    assert len(base) == len(left) + len(right) and gcd(m, n) == gcd(v, n) == 1
    mod = n * n
    counts = dict(first=0, nonpositive=0, nonunit=0, empty_interval=0,
                  right_candidates=0, arithmetic_completions=0)
    hits = []
    for a in primes:
        if a > first_bound:
            break
        if a in base:
            continue
        counts["first"] += 1
        A, U = m * a, md * a + m
        k = A * n - U * v
        if k <= 0:
            counts["nonpositive"] += 1
            continue
        if gcd(k, mod) != 1:
            counts["nonunit"] += 1
            continue
        residue = (v * A * pow(k, -1, mod)) % mod
        floor = max(a + 1, (v * A) // k + 1)
        b0 = floor + (residue - floor) % mod
        r0, rr = divmod(k * b0 - v * A, mod)
        q0, rq = divmod(U * b0 + A, n)
        assert rr == rq == 0 and r0 > 0 and q0 > 0

        # For any eligible b >= b0, the right pair c<=d has sum r and
        # product q. R(b)=q/r decreases strictly towards n*U/k. Since
        # c<=2R(b) and c-R(b)=c*c/r, c is in this interval for every b.
        c_min = max(2, (n * U) // k + 1, a + 1 if globally_first else 2)
        c_max = (q0 * r0**2 + 4 * q0**2) // r0**3
        if c_min > c_max:
            counts["empty_interval"] += 1
            continue
        for c in range(c_min, c_max + 1):
            counts["right_candidates"] += 1
            # The symmetric breeder equation recovers d uniquely for c.
            d, rem = divmod(A * A + n * U * c, k * c - n * U)
            if rem or d <= c:
                continue
            b, rem = divmod(n * c * d - A, U)
            if rem or b < b0 or (b - residue) % mod:
                continue
            assert A * b == v * c * d + n * (c + d)
            counts["arithmetic_completions"] += 1
            if len({a, b, c, d}) != 4 or base.intersection((a, b, c, d)):
                continue
            if all(is_prime(p) for p in (b, c, d)):
                hits.append((a, b, c, d))
    return counts, hits


def tail_exclusion(left, right, lower_a):
    m, n = prod(left), prod(right)
    md = sum(m // p for p in left)
    v = sum(n // q for q in right)
    s_left = Fraction(md, m)
    s_right = Fraction(v, n)
    W = 1 / (1 / s_left - s_right)
    larger_left = s_left + Fraction(2, lower_a)
    delta = 1 / larger_left - s_right
    assert delta > 0
    R_high = 1 / delta

    # Write q=cd, r=c+d and R=q/r. The two cross equations yield
    # R=1/(1/(s_left+1/a+1/b)-s_right), so W<R<=R_high when b>a>=lower_a.
    # Also q>md*lower_a²/n, hence r=q/R>md*lower_a²/(n*R_high).
    # Combining c<=2R and c-R=c²/r gives this a-independent bound.
    upper = R_high + 4 * n * R_high**3 / (md * lower_a**2)
    first_possible = W.numerator // W.denominator + 1
    next_prime = first_possible
    while not is_prime(next_prime):
        next_prime += 1
    assert upper < next_prime
    return first_possible, upper.numerator // upper.denominator, next_prime


def main():
    cutoff = 300_000
    primes = primes_through(cutoff)
    # Put the side not containing 2 on the left. On this orientation the
    # asymptotic interval meets a larger prime gap and the cutoff is smaller.
    right, left = balanced_base(primes)
    tail = tail_exclusion(left, right, cutoff)
    counts, hits = two_pair_candidates(left, right, primes, cutoff - 1)
    assert counts == dict(first=25_939, nonpositive=80, nonunit=10_986,
                          empty_interval=14_873, right_candidates=0,
                          arithmetic_completions=0), counts
    assert tail == (793, 796, 797)
    assert not hits, hits
    print("Left base:", left)
    print("Right base:", right)
    print(f"For a >= {cutoff} the smallest right prime must lie from {tail[0]} through {tail[1]}.")
    print("The next prime is", tail[2])
    print("For a <", cutoff, "counts:", counts)
    print("Two-by-two prime completions:", len(hits))


if __name__ == "__main__":
    main()
