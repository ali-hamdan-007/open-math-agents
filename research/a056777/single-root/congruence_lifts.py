#!/usr/bin/env python3
"""Replay congruence filters of the #9935 p=q=2 (mod 5) branch."""
from itertools import product
from math import isqrt


def cubic(p, q, x):
    a = p*p+p+1
    first = a*(q+1)+2*p**3
    second = 2*p**3*(p+q-1)+first-2
    return ((2*x-first)*x+second)*x-2*(p**4*q+12)


def square5(discriminant):
    return discriminant % 5 in (0, 1, 4)


def roots_two(p, q):
    """Allowed x modulo 4 from the cubic modulo 64."""
    classes = set()
    if (p % 16 == 7 or (p % 16 == 15 and q % 16 == 11)):
        classes.add(1)
    if q % 32 == 19 or (p % 8 == 7 and q % 32 == 3):
        classes.add(3)
    return classes


def legendre_sign_at_x(q, x4, x3):
    """Required character of x modulo q, from x | p^4*q+12."""
    assert q % 4 == 3 and x4 in (1, 3) and x3 in (1, 2)
    return 1 if (x4, x3) in ((1, 1), (3, 2)) else -1


def check_two():
    survivors = 0
    for p, q in product(range(3, 64, 4), range(3, 64, 8)):
        roots32 = {x % 4 for x in range(1, 32, 2) if cubic(p, q, x) % 32 == 0}
        assert (1 in roots32) == (p % 8 == 7)
        assert (3 in roots32) == (q % 16 == 3)
        roots64 = {x % 4 for x in range(1, 64, 2) if cubic(p, q, x) % 64 == 0}
        assert roots64 == roots_two(p, q)
        survivors += bool(roots64)
    print(f'mod 64: {survivors}/128 (p,q) classes survive')


def check_five():
    survivors = 0
    for v, w in product(range(5), repeat=2):
        p, q = 2+5*v, 12+25*w
        d = 2*(v-1)**2+w+2
        xs = []
        for u in range(5):
            x = 1+5*u
            f = cubic(p, q, x)
            assert (f - 25*(-u*u+(1-v)*u-v*v+2*v-w+2)) % 125 == 0
            if f % 125 == 0:
                xs.append(x)
        assert bool(xs) == square5(d)
        assert len(xs) == (1 if d % 5 == 0 else 2 if square5(d) else 0)
        survivors += bool(xs)
    print(f'mod 125 with x == 1 (mod 5): {survivors}/25 lift classes survive')



def check_five_singular():
    cases = 0
    for p, q in product(range(2, 125, 5), range(12, 125, 25)):
        v, w = (p-2)//5, (q-12)//25
        if (2*(v-1)**2+w+2) % 5 != 0:
            continue
        u0 = (3*(1-v)) % 5
        x0 = 1+5*u0
        n = cubic(p, 0, x0)
        t = n-cubic(p, 1, x0)
        expected = (n*pow(t, -1, 625)) % 625
        assert expected % 125 == q
        for q_lift in range(q, 625, 125):
            for x_lift in range(x0, 125, 25):
                assert (cubic(p, q_lift, x_lift) % 625 == 0) == (q_lift == expected)
        cases += 1
    print(f'mod 625 in the double-root case: one q lift for each of {cases} classes')


def is_prime(n):
    return n >= 2 and all(n % t for t in range(2, isqrt(n)+1))


def reciprocal_example():
    # q % 3 == 1 fixes x % 3 == 1 by #9935. These examples meet
    # the known restrictions on p,q and have simple nonzero roots mod q.
    for q in range(4000, 5000):
        if (q % 8, q % 5, q % 9) != (3, 2, 4) or not is_prime(q):
            continue
        for p in range(2*q+1, isqrt((q**3-1)//7)+1):
            if (p % 4, p % 5, p % 3) != (3, 2, 2) or not is_prime(p):
                continue
            if 7*p*p >= q**3 or 2*p*q+q*q >= p*p:
                continue
            x4s = roots_two(p, q)
            if len(x4s) != 1:
                continue
            required = legendre_sign_at_x(q, next(iter(x4s)), 1)
            xs = [x for x in range(1, q) if cubic(p, q, x) % q == 0]
            if not xs or any(pow(x, (q-1)//2, q) == required % q for x in xs):
                continue
            lifts = sorted(x for r in xs for x in range(r+q, p, q)
                           if x >= q+12 and x % 3 == 1 and x % 4 in x4s
                           and cubic(p, q, x) % 64 == 0 and is_prime(x)
                           and (x % 5 == 4 or (x % 5 == 1 and q % 25 == 12))
                           and cubic(p, q, x) % 125 == 0)
            if not lifts:
                continue
            a = p*p+p+1
            assert all((6*x*x-2*(a+2*p**3)*x+2*p**4+a-2) % q for x in xs)
            print(f'reciprocity example: p={p}, q={q}, x mod 4 in {x4s}, '
                  f'cubic roots mod q: {xs}, required character: {required}; lifts: {lifts}')
            return
    raise AssertionError('no example found')


if __name__ == '__main__':
    check_two()
    check_five()
    check_five_singular()
    reciprocal_example()
