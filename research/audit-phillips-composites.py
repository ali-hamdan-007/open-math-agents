#!/usr/bin/env python3
"""Check a composite on each side of Phillips's published Erdős 307 certificate."""
from math import prod
from pathlib import Path
from sys import argv

q_line, p_line, *deviations = Path(argv[1]).read_text().splitlines()
q = [int(x) for x in q_line.split()[1:]]
p = [int(x) for x in p_line.split()[1:]]
deltas = [int(x) for x in deviations]
assert q_line.startswith("Q ") and p_line.startswith("P0 ")
assert len(q) == 4 and len(p) == 54 and len(deltas) == 914
assert deltas[-1] == 1
N = prod(q)
V = sum(N // x for x in q)
M0 = prod(p)

E = V * M0
for delta, following in zip(deltas[:3], deltas[1:4]):
    new, rem = divmod(E + following, delta)
    assert rem == 0
    E *= new
assert new == 409 * 12553

prime_factor = 3733
modulus = prime_factor * prod(deltas[:-1])
E = V * M0 % modulus
for delta, following in zip(deltas, deltas[1:]):
    new, rem = divmod(E + following, delta)
    assert rem == 0
    modulus //= delta
    E = E * new % modulus
assert modulus == prime_factor
inverse = pow(V, -1, modulus)
M = E * inverse % modulus
U = (N * M - 1) * inverse % modulus
assert (N * U + M * M) % modulus == 0
assert M0 * M0 > prime_factor

print(f"Third left addition: {409} × {12553}")
print(f"Closing right member modulo {prime_factor}: 0")
