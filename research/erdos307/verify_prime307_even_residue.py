#!/usr/bin/env python3
"""Exact even-support residue filter and tail mass bounds for prime-only #307.

For an even squarefree support 2W, let k count its odd primes and let m
count those congruent to 3 mod 4. Every odd prime's cofactor is a square
modulo that prime. Multiply the Legendre symbols and apply quadratic
reciprocity to get (2/W)=(-1)**(m*(m-1)//2). The support cofactor sum is
a sum of one even square and one odd square, hence 5 mod 8. The cofactor
sum is W(1+2*k+4*m) mod 8 because odd residues are self-inverse mod 8.
"""

from bisect import bisect_left
from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod

from search_true_prime_two_pairs import primes_through

ODD_RESIDUES = (1, 3, 5, 7)


def admissible(k, m, w):
    return (
        w % 4 == (-1)**m % 4
        and w * (1 + 2*k + 4*m) % 8 == 5
        and (1 if w in (1, 7) else -1) == (-1)**(m*(m-1)//2)
    )


def residue_patterns(base, additions):
    odd = base[1:]
    k = len(odd)
    m = sum(p % 4 == 3 for p in odd)
    w = prod(p % 8 for p in odd) % 8
    for tail in product(ODD_RESIDUES, repeat=additions):
        if admissible(k + additions, m + sum(p % 4 == 3 for p in tail),
                      w * prod(tail) % 8):
            yield tail


def max_mass_given_floor(primes, patterns, lower, large):
    """Maximal mass with each tail >= lower and at least one tail > large."""
    by_class = {r: [p for p in primes if p % 8 == r] for r in ODD_RESIDUES}
    lengths = len(patterns[0])
    best = Fraction(0)
    for residues in patterns:
        # Permutations are present, so assign the last residue to the large
        # prime. For each other residue class the smallest distinct primes
        # from that class maximize its possible mass.
        counts = Counter(residues[:-1])
        small = []
        for r, count in counts.items():
            options = by_class[r]
            start = bisect_left(options, lower)
            small.extend(options[start:start + count])
        options = by_class[residues[-1]]
        large_prime = options[bisect_left(options, large + 1)]
        assert len(small) == lengths - 1 and len(set(small + [large_prime])) == lengths
        best = max(best, sum((Fraction(1, p) for p in small + [large_prime]), Fraction(0)))
    return best


def main():
    table = [(k, m, w) for k in range(4) for m in range(4)
             for w in ODD_RESIDUES if admissible(k, m, w)]
    assert table == [(0, 2, 5), (1, 3, 3), (2, 0, 1), (3, 1, 7)]
    assert all((k - m) % 4 == 2 for k, m, _ in table)

    base = primes_through(271)
    assert sum(p % 4 == 1 for p in base[1:]) == 26
    allowed = [list(residue_patterns(base, n)) for n in range(5)]
    print("Ordered residue patterns for 0–4 new primes:", [len(x) for x in allowed])
    assert [len(x) for x in allowed] == [0, 1, 2, 4, 16]
    assert all(all(p % 4 == 3 for p in tail) for n in (1, 2, 3) for tail in allowed[n])
    assert all(len({p % 4 for p in tail}) == 1 for tail in allowed[4])

    example = (283, 307, 311)
    assert all(p in primes_through(311) for p in example)
    assert sum((Fraction(1, p) for p in base + list(example)), Fraction(0)) > 2
    assert [tail[-1] for tail in allowed[4] if tail[:-1] == tuple(p % 8 for p in example)] == [3]
    print("Partial support with 283, 307, 311 has mass >2; the remaining prime is 3 mod 8.")

    primes = primes_through(100_300)
    deficit = 2 - sum((Fraction(1, p) for p in base), Fraction(0))
    for n in (3, 4):
        modes = (3,) if n == 3 else (1, 3)
        for mode in modes:
            patterns = [p for p in allowed[n] if p[0] % 4 == mode]
            choices = [p for p in primes if 271 < p <= 2400 and p % 4 == mode]
            possible = [p for p in choices if
                        max_mass_given_floor(primes, patterns, p, 100_000) >= deficit]
            cap = max(possible)
            larger = next(p for p in primes if p > cap and p % 4 == mode)
            assert max_mass_given_floor(primes, patterns, larger, 100_000) < deficit
            print(f"{n} new primes, all {mode} mod 4: smallest at most {cap}.")


if __name__ == "__main__":
    main()
