#!/usr/bin/env python3
"""Independently compare the C++ search with a trial-division reference."""

import csv
import re
import subprocess
import sys
from collections import defaultdict
from math import isqrt


def trial_invariants(n):
    remaining = n
    omega = 0
    phi = n
    shape = []
    for p in range(2, isqrt(n) + 1):
        if p * p > remaining:
            break
        if remaining % p:
            continue
        phi -= phi // p
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        omega += exponent
        shape.append(exponent)
    if remaining > 1:
        phi -= phi // remaining
        omega += 1
        shape.append(1)
    return omega, phi, "".join(map(str, sorted(shape, reverse=True)))


def divisor_sum(n):
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sum(small) + sum(n // d for d in small if d * d != n)


def main():
    executable = sys.argv[1]
    limit = 100_000
    values = {n: trial_invariants(n) for n in range(2, limit + 13)}
    observed = defaultdict(lambda: [0] * 8)
    for n in range(2, limit + 1):
        m = n + 12
        on, pn, sn = values[n]
        om, pm, sm = values[m]
        if (on, om) not in {(3, 4), (4, 3)}:
            continue
        ph = pm - pn == 12
        si = divisor_sum(m) - divisor_sum(n) == 12
        for key in (f"{on}->{om}", f"{sn}->{sm}"):
            row = observed[key]
            row[0] += 1
            column = {(True, False): 1, (False, True): 2, (True, True): 3}.get((ph, si), 4)
            row[column] += 1
            if column < 4 and row[4 + column] == 0:
                row[4 + column] = n

    output = subprocess.check_output([executable, str(limit)], text=True)
    rows = csv.reader(line for line in output.splitlines()[1:] if not line.startswith("example"))
    next(rows)
    recorded = {shape: list(map(int, fields)) for shape, *fields in rows}
    if recorded != observed:
        raise ValueError("C++ and trial-division results differ.")
    print(f"Trial-division audit matched every C++ row for 2≤n≤{limit}.")

    full_output = subprocess.check_output([executable], text=True)
    examples = [row for row in full_output.splitlines() if row.startswith("example")]
    for row in examples:
        matched = re.fullmatch(
            r"example (\d+)=[^,]*, (\d+)=[^;]*; phi (\d+),(\d+); sigma (\d+),(\d+)", row
        )
        if matched is None:
            raise ValueError(f"Could not parse example {row}")
        n, m, phi_n, phi_m, sigma_n, sigma_m = map(int, matched.groups())
        on, pn, _ = trial_invariants(n)
        om, pm, _ = trial_invariants(m)
        if (m != n + 12 or (on, om) not in {(3, 4), (4, 3)}
                or (pn, pm, divisor_sum(n), divisor_sum(m)) !=
                (phi_n, phi_m, sigma_n, sigma_m)
                or not (phi_m - phi_n == 12 or sigma_m - sigma_n == 12)):
            raise ValueError(f"Invalid example {row}")
    print(f"Independently verified all {len(examples)} reported full-range survivors.")


if __name__ == "__main__":
    main()
