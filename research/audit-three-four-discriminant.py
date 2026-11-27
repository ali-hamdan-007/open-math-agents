#!/usr/bin/env python3
"""Independent exact symbolic audit. Requires SymPy."""
import sympy as sp

p, r, q, A, B, D, P, J = sp.symbols("p r q A B D P J")
phi3 = p * (p - 1) * (q - 1)
phi4 = r * (r - 1) * (B - A + 1)
sigma3 = (1 + p + p**2) * (q + 1)
sigma4 = (1 + r + r**2) * (B + A + 1)
gap = r**2 * B - p**2 * q
solution = sp.solve(
    [gap - D, phi3 - phi4 + gap, sigma3 - sigma4 + gap], (q, A, B)
)
H = r * (r**2 - (p + 1) * r - 2 * p)
N = H * (2 * p + 1) + (2 * p**2 + 4 * p) * r**2 + 3 * p**2 * r + p**2 * (p - 1) - D
L = r**2 - p**2
M = p**2 * (2 * r + 1) * N + (p**2 * (2 * r**2 - 2 * p) + D) * H
assert sp.cancel(solution[A] - N / H) == 0
assert sp.cancel(solution[B] - M / (H * L)) == 0
assert sp.cancel((4 * solution[B] - solution[A]**2) * H**2 * L - (4 * M * H - N**2 * L)) == 0
# Positivity of denominators already at p >= 7 and r >= p+4.
for denominator in (H, L):
    shifted = sp.Poly(denominator.subs(r, p + J + 4).subs(p, P + 7), P, J)
    assert shifted.coeff_monomial(1) > 0 and min(shifted.coeffs()) > 0
for d in (12, -12):
    polynomial = sp.Poly((4 * M * H - N**2 * L).subs(D, d).subs(r, p + 6 + J).subs(p, P + 7), P, J)
    assert len(polynomial.terms()) == 61 and min(polynomial.coeffs()) == 4
    assert polynomial.coeff_monomial(1) == {12: 11111035680, -12: 10960405920}[d]
    assert sp.rem(p**2 * (p - 1) - d, p + 4, p) == -80 - d
    repeated = [prime for prime in sp.factorint(80 + d) if prime >= 11]
    assert repeated == [{12: 23, -12: 17}[d]]
    rr, pp = repeated[0], repeated[0] - 4
    moment = solution[A].subs({p: pp, r: rr, D: d})
    assert moment == {12: sp.Rational(20928, 31), -12: sp.Rational(7932, 25)}[d]
    print(f"D={d}: 61 positive coefficients; four-gap candidate p={pp}, r={rr}, A={moment}")
