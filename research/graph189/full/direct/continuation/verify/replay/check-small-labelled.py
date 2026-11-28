"""Check full labelled orbit coverage against the canonical small-k index."""
from itertools import combinations, permutations, product
import json
from pathlib import Path

base = Path(__file__).resolve().parents[2] / "global" / "cut3"
pairs = list(combinations(range(3), 2))
keys = set()
labelled_count = 0
for distances in product(range(1, 6), repeat=3):
    if 2 * max(distances) > sum(distances):
        continue
    distance = dict(zip(pairs, distances))
    for low in [0, 1, 2, "none", "A", "B"]:
        if any(value > 4 and low not in pair for pair, value in distance.items()):
            continue
        for degree, large_side in product(range(9, 16), (0, 1)):
            labelled_count += 1
            for permutation in permutations(range(3)):
                triangle = [distance[tuple(sorted((permutation[i], permutation[j])))] for i, j in pairs]
                if triangle == sorted(triangle):
                    canonical_low = str(permutation.index(low)) if isinstance(low, int) else low
                    keys.add(("".join(map(str, triangle)), canonical_low, 2, large_side, degree))
rows = [json.loads(line) for line in (base / "small-three-cases.jsonl").read_text().splitlines()]
assert set(tuple(row[:5]) for row in rows) == keys
assert labelled_count == 5376 and len(keys) == len(rows) == 1652
assert all(row[-1] == "unsat" for row in rows)
print(f"{labelled_count} labelled cases, {len(keys)} stored UNSAT representatives.")
