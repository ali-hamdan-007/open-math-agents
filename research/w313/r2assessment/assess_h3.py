"""Measure the direct and propagation coverage of the verified W(3,13) clauses."""
from collections import Counter
from itertools import product
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / "window141"))
from r2_screen import propagate, r2_case

sys.path.insert(0, str(here.parent / "r2geometry"))
from classify import WINDOWS, embeddings

verified = {pattern for width, seed in WINDOWS for pattern in embeddings(width, seed)}
for start, end in ((0, 15), (24, 39), (52, 65), (78, 91), (104, 119), (128, 143)):
    verified.update((a, a + 2, a + 14, a + 16) for a in range(start, end + 1))

clauses = tuple(sum(1 << x for x in pattern) for pattern in sorted(verified))
counts = Counter()
differences = Counter()
direct = []
extra = []
for heights in product(range(13), repeat=4):
    if r2_case(*heights) != "H3":
        continue
    i, j, k, l = heights
    seeds = tuple(13 * h + c for c, h in enumerate(heights))
    mask = sum(1 << x for x in seeds)
    counts["normalized"] += 1
    counts["reflection-fixed"] += i + l == j + k == 12
    if any(mask & clause == clause for clause in clauses):
        direct.append(heights)
    elif not propagate(seeds, clauses):
        extra.append(heights)
    else:
        counts["remaining"] += 1
        differences[(i - k, j - l)] += 1
        if i == k and j == l:
            counts["remaining alternating"] += 1

assert counts["normalized"] == 4924
assert direct == [(h, h + 1, h, h + 1) for h in range(6)]
print("Certified four-red clauses:", len(clauses))
print("H3:", dict(counts))
print("Direct fits:", direct)
print("Additional eliminations by propagation:", len(extra), extra[:10])
print("Remaining height-difference classes:", len(differences))
print("Largest classes:", differences.most_common(10))
