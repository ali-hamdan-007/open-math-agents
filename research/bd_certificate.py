"""Find and audit two denominator certificates for the Pell logarithms.

Requires mpmath. Interval endpoints are converted to exact binary rationals;
all certificate comparisons use fractions.Fraction.
"""
import json
from fractions import Fraction

from mpmath import iv, mp


def fraction_from_mpf(raw):
    sign, mantissa, exponent, _ = raw
    numerator = -mantissa if sign else mantissa
    return Fraction(numerator) * Fraction(2) ** exponent


def endpoints(interval):
    return tuple(fraction_from_mpf(raw) for raw in interval._mpi_)


def coefficients():
    sqrt3, sqrt8 = iv.sqrt(3), iv.sqrt(8)
    log_v = iv.ln(3 + sqrt8)
    seed3 = 1 + 1 / sqrt3
    shifts = [1 + 1 / sqrt8, 2 + 5 / sqrt8]
    return endpoints(log_v), endpoints(iv.ln(2 + sqrt3) / log_v), [
        endpoints(iv.ln(seed3 / shift) / log_v) for shift in shifts
    ]


def convergents(real):
    p_old, p = 0, 1
    q_old, q = 1, 0
    while real.denominator > 0:
        a = real.numerator // real.denominator
        p_old, p = p, a * p + p_old
        q_old, q = q, a * q + q_old
        yield p, q
        remainder = real - a
        if not remainder:
            break
        real = 1 / remainder


def floor(value):
    return value.numerator // value.denominator


def certificate(p, q, theta, phis, tolerance, margin):
    error = max(abs(q * endpoint - p) for endpoint in theta)
    ks = [floor(q * lower) for lower, _ in phis]
    separations = [
        min(q * lower - k, k + 1 - q * upper)
        for (lower, upper), k in zip(phis, ks, strict=True)
    ]
    if error >= tolerance or min(separations) <= margin:
        return None
    return {
        'p': str(p), 'q': str(q), 'k': [str(k) for k in ks],
        'error_upper_decimal': mp.nstr(mp.mpf(error.numerator) / error.denominator, 12),
        'separation_lower_decimals': [
            mp.nstr(mp.mpf(value.numerator) / value.denominator, 12)
            for value in separations
        ],
    }


def main():
    iv.dps = 1200
    mp.dps = 50
    log_v, theta, phis = coefficients()
    assert log_v[0] > 1
    assert Fraction(747105379, 10**9) <= theta[0] <= theta[1] <= Fraction(747105381, 10**9)
    assert Fraction(86803, 10**6) <= phis[0][0] <= phis[0][1] <= Fraction(86805, 10**6)
    assert Fraction(-493966, 10**6) <= phis[1][0] <= phis[1][1] <= Fraction(-493965, 10**6)
    for p, q in convergents(sum(theta) / 2):
        if q > 10**510:
            raise RuntimeError('No denominator found in the requested range')
        if q < 10**489:
            continue
        first = certificate(p, q, theta, phis, Fraction(1, 10**488), Fraction(1, 4))
        if first:
            break
    assert q <= 10**496
    assert Fraction(10**487, 10**488) + Fraction(q, 10**497) < Fraction(1, 4)
    assert Fraction(5, 24 * 4**850) < Fraction(1, 10**497)
    second = certificate(1226, 1641, theta, phis, Fraction(1, 10000), Fraction(1, 4))
    assert second
    assert Fraction(850, 10000) + Fraction(1641, 10000) < Fraction(1, 4)
    assert Fraction(5, 24 * 4**6) < Fraction(1, 10000)
    print(json.dumps({'first': first, 'second': second, 'conditional_index_bound': 5}, indent=2))


if __name__ == '__main__':
    main()
