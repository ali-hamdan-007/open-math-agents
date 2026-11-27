#!/usr/bin/env python3
"""Exclude every allocation of at most four new primes for the 1,625 base splits.

Both orientations are checked. The 2+2 distribution uses the earlier exact
verifier. For 0+4 the divisibility gate is enough. For 1+3 the smallest
addition is bounded: when on the singleton side a cofactor gate suffices;
when on the triple side, absorb it into the right base and close 1+2.
The same minimum absorption reduces 1+2 to the original 1+1 frame.
"""

from collections import Counter
from fractions import Fraction
from math import gcd, prod

from search_true_prime_two_pairs import one_by_two_candidates, primes_through
from search_true_prime_two_pair_swaps import main as verify_two_plus_two
from search_true_prime_two_pair_swaps import split_family


def verify_asymmetric():
    base = primes_through(271)
    deficit = 2 - sum((Fraction(1, p) for p in base), Fraction(0))
    bound = 4 // deficit
    assert bound == 3_174
    added = [p for p in primes_through(bound) if p not in base]
    counts = Counter()
    asymmetric = Counter()
    three_additions = Counter()
    for _, left, right in split_family(base):
        counts["splits"] += 1
        for left, right in ((left, right), (right, left)):
            m, n = prod(left), prod(right)
            u = sum(m // p for p in left)
            v = sum(n // p for p in right)
            assert gcd(m, n) == gcd(v, n) == 1

            # 0+4: the fixed left numerator is the product of all right
            # denominators, hence is necessarily divisible by the right base.
            counts["zero_plus_four"] += 1
            assert u % n, ("unresolved 0+4 product gate", left, right)

            for p in added:
                # 1+3 with the smallest new prime on the singleton side:
                # the new left numerator is likewise divisible by n.
                counts["singleton_min"] += 1
                assert (u * p + m) % n, ("unresolved 1+3 product gate", left, right, p)

                # 1+3 with smallest new prime on the triple side. After
                # absorbing it into that side, the remaining three additions
                # must be greater and solve precisely the 1+2 equation.
                counts["triple_min"] += 1
                nr, vr = n * p, v * p + n
                candidates = list(one_by_two_candidates(
                    m, u, nr, vr, p + 1, p + 1, asymmetric))
                assert not candidates, ("unresolved 1+2 candidate", left, right, p, candidates)

                # 1+2 with the smallest addition on the pair side. The
                # absorbed frame has a unique solution for its two slots.
                delta = m * nr - u * vr
                if delta <= 0:
                    three_additions["nonpositive"] += 1
                else:
                    a, rem_a = divmod(m * vr + nr * nr, delta)
                    if rem_a:
                        three_additions["nonintegral"] += 1
                    else:
                        b, rem_b = divmod(u * nr + m * m, delta)
                        assert rem_b == 0
                        if min(a, b) <= p:
                            three_additions["minimum_order"] += 1
                        else:
                            raise AssertionError(("unresolved 1+1 candidate", left, right, p, a, b))
    assert counts["splits"] == 1_625
    print("Asymmetric allocation checks:", dict(counts))
    print("Triple-side minimum outcomes:", dict(asymmetric))
    print("Pair-side minimum outcomes for three additions:", dict(three_additions))


if __name__ == "__main__":
    verify_asymmetric()
    verify_two_plus_two()
    print("Completions with up to four primes across all allocations: 0")
