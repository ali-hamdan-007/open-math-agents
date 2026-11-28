"""Verify a direct near-spanning path for each degree-four terminal key."""
from itertools import permutations
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
CATALOGUE = HERE.parent / "moderate-certs" / "patterns-4.json"


def bits(mask):
    return tuple(i for i in range(mask.bit_length()) if (mask >> i) & 1)


def short_path(p, c, j, exterior, z):
    if j < c:
        other_arm = list(range(p - 1, c - 1, -1))
        choices = [list(range(j, c)), list(range(j, -1, -1))]
    else:
        other_arm = list(range(c + 1))
        choices = [list(range(j, c, -1)), list(range(j, p))]
    return other_arm + [p + x for x in exterior] + [z] + max(choices, key=len)


records = json.loads(CATALOGUE.read_text())
assert len(records) == 30
count = 0
for row in records:
    p, b, n = (row[k] for k in ("p", "b", "n"))
    ext, contact = row["ext"], row["contacts"]
    positions = {i for mask in contact for i in bits(mask)}
    assert len(positions) == 1
    c, = positions
    assert max(c, p-c-1) <= 6
    ports = {x for x, mask in enumerate(contact) if mask}
    forced = {x for x in range(b) if ext[x].bit_count()+contact[x].bit_count()==3}
    assert n == p+b+1
    z = n-1
    for mask in range(1, 1 << b):
        zports = set(bits(mask))
        if not forced <= zports:
            continue
        if len(ports) == len(zports) == 1 and ports == zports:
            continue
        route = next(q for q in permutations(range(b))
                     if q[0] in ports and q[-1] in zports
                     and all(ext[x] & (1 << y) for x, y in zip(q, q[1:])))
        for j in range(p):
            if j == c:
                continue
            path = short_path(p, c, j, route, z)
            mandatory = list(row["lower"])
            for u in (p+route[-1], j):
                mandatory[z] |= 1 << u
                mandatory[u] |= 1 << z
            assert len(path) >= n-2
            assert len(path) == len(set(path))
            assert all(mandatory[u] & (1 << v) for u, v in zip(path, path[1:]))
            count += 1
print(f"{len(records)} layouts, {count} admissible z-neighborhood / path-site combinations")
