from math import isqrt, lcm

SCALE = 10**12
LIMIT = 12000000

def prefixes(ell, odd_primes):
    result = [[0] for _ in range(ell)]
    for p in odd_primes:
        if p != ell:
            prefix = result[p % ell]
            prefix.append(prefix[-1] + (SCALE + p - 1)//p)
    return result

def sieve_primes(limit):
    sieve = bytearray(b'\1') * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit-p*p)//p + 1)
    return [p for p in range(3, limit + 1, 2) if sieve[p]]

def single_width(m, d):
    return max(0, (m+1)//d - 1)

def pair_caps(r, prefixes, reserved, ell, fast=True):
    budget = ell - 2
    order = next(k for k in range(1, ell) if pow(r, 2*k, ell) == 1)
    d = lcm(2, order)
    scores = [[0] * (reserved+1) for _ in range(budget+1)]
    left, right = prefixes[r], prefixes[-r]
    assert min(len(left), len(right)) > d*(budget+2)-2+reserved
    for q, score in enumerate(scores):
        cap = d*(q+2)-2
        # Below the breakpoint, check every m. Above it, n is constant
        # on each interval where the single-class width is constant.
        candidates = range(cap+1)
        if fast and cap > d+2*q:
            candidates = list(range(d+2*q+1))
            candidates.extend(endpoint for k in range(q+1)
                              if (endpoint := d*(k+2)-2) > d+2*q)
        for m in candidates:
            n = d*(q-single_width(m,d)+2)-2
            if m > q:
                n = min(n, max(q, 2*q+d-m))
            for c in range(reserved+1):
                score[c] = max(score[c], *(left[m+i]+right[n+c-i] for i in range(c+1)))
    return scores

def bound(reserved, prefixes, ell, fast=True):
    budget = ell - 2
    table = [[0] * (reserved+1) for _ in range(budget+1)]
    for r in range(1, (ell+1)//2):
        caps = pair_caps(r, prefixes, reserved, ell, fast)
        table = [[max(table[q-used][c-fixed]+caps[used][fixed]
                      for used in range(q+1) for fixed in range(c+1))
                  for c in range(reserved+1)] for q in range(budget+1)]
    return table[-1][-1]

if __name__ == '__main__':
    import sys

    expected = {
        43: (1901542459432, 1905724184659),
        47: (1959652795054, 1961729716046),
        53: (1914109004976, 1916876427065),
        59: (2017301458398, 2018597941994),
        61: (1917259307598, 1920571962656),
        67: (2015340263771, 2017570942082),
        71: (2032151038624, 2033929319752),
        73: (1944601903506, 1947278638477),
    }
    odd_primes = sieve_primes(LIMIT)
    selected = list(map(int, sys.argv[1:])) or list(p for p in odd_primes if 43 <= p <= 73)
    for ell in selected:
        assert ell in odd_primes
        data = prefixes(ell, odd_primes)
        for index, reserved in enumerate((0, 6)):
            upper = bound(reserved, data, ell)
            if ell in expected:
                assert upper == expected[ell][index]
            if ell == 43:
                assert upper == bound(reserved, data, ell, fast=False)
            print(ell, reserved, upper, upper < 2*SCALE, flush=True)
