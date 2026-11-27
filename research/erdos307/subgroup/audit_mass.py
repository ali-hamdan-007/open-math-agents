from math import isqrt, lcm

LIMIT = 3000000
SCALE = 10**10
is_prime = bytearray(b"\1") * (LIMIT + 1)
for p in range(2, isqrt(LIMIT) + 1):
    if is_prime[p]:
        is_prime[p*p:LIMIT+1:p] = bytes((LIMIT-p*p)//p + 1)
primes = [p for p in range(3, LIMIT + 1, 2) if is_prime[p]]

def bound(ell, reserved):
    budget = ell - 2
    best = [[0] * (reserved + 1) for _ in range(budget + 1)]
    prefixes = [[0] for _ in range(ell)]
    for prime in primes:
        row = prefixes[prime % ell]
        row.append(row[-1] + (SCALE + prime - 1) // prime)
    for residue in range(1, ell):
        square = residue**2 % ell
        order, power = 1, square
        while power != 1:
            order, power = order + 1, power * square % ell
        step = lcm(2, order)
        prefix = prefixes[residue]
        assert len(prefix) > step * (budget + 2) - 2 + reserved
        best = [
            [max(best[q - used][c - fixed] + prefix[step * (used + 2) - 2 + fixed]
                 for used in range(q + 1) for fixed in range(c + 1))
             for c in range(reserved + 1)]
            for q in range(budget + 1)
        ]
    return best[budget][reserved]

for ell in [31, 37, 41, 43]:
    for reserved in [0, 6]:
        upper = bound(ell, reserved)
        print(ell, reserved, upper, flush=True)
        if ell <= 41:
            assert upper < 2 * SCALE
