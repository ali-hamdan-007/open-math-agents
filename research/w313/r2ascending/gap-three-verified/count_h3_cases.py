"""Count the normalized height tuples in the exact R2.H3 statement."""
from collections import Counter
from itertools import product

counts = Counter()
for i, j, k, l in product(range(13), repeat=4):
    if not (i + k < 2 * j and 2 * k < j + l):
        continue
    if not (i + l < 12 or (i + l == 12 and j + k <= 12)):
        continue
    if i == k and j == l:
        counts[min(j - i, 4)] += 1
    else:
        counts["nonalternating"] += 1

for gap in range(1, 4):
    print(f"gap {gap}: {counts[gap]}")
print(f"gap at least 4: {counts[4]}")
print(f"nonalternating: {counts['nonalternating']}")
print(f"total: {sum(counts.values())}")
