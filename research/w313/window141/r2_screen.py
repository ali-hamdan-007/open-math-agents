"""Measure unit-propagation pruning on the current R2 ray hypotheses."""
from collections import Counter
from itertools import product

from coverage import clause_sets

SIZE = 160
FULL = (1 << SIZE) - 1
RAYS = tuple(tuple(13 * row + column for row in range(13)) for column in range(4))
APS = tuple(sum(1 << (a + d * i) for i in range(13))
            for d in range(1, 13) for a in range(SIZE - 12 * d))


def third_points(a, b):
    if a == b:
        return 0
    candidates = {2 * a - b, 2 * b - a}
    if (a + b) % 2 == 0:
        candidates.add((a + b) // 2)
    return sum(1 << x for x in candidates if 0 <= x < SIZE)


PAIR_BANS = tuple(tuple(third_points(a, b) for b in range(SIZE)) for a in range(SIZE))
WINDOW141_CLAUSES = tuple(sum(1 << p for p in clause)
                    for clause in clause_sets([(43, 20), (73, 20)], True))


R2_CLAUSES = tuple(sum(1 << p for p in clause)
                   for clause in clause_sets((), False, range(51, 95)))


def r2_case(i, j, k, l):
    first = i + k - 2 * j
    second = j + l - 2 * k
    earlier = (i + l, j + k) <= (12, 12)
    if first > 0 and second > 0:
        return "H1"
    if first > 0 and second < 0 and earlier:
        return "H2"
    if first < 0 and second > 0 and earlier:
        return "H3"
    return None


def propagate(seeds, clauses):
    allowed = FULL
    reds = []
    mask = 0

    def mark(p):
        nonlocal mask, allowed
        bit = 1 << p
        if not allowed & bit:
            return False
        for q in reds:
            allowed &= ~PAIR_BANS[p][q]
        reds.append(p)
        mask |= bit
        return True

    for p in seeds:
        if not mark(p):
            return False
    while True:
        for clause in clauses:
            missing = clause & ~mask
            if missing == 0:
                return False
            if missing & (missing - 1) == 0:
                allowed &= ~missing
        for progression in APS:
            if progression & mask:
                continue
            candidates = progression & allowed
            if candidates == 0:
                return False
            if candidates & (candidates - 1) == 0:
                if not mark(candidates.bit_length() - 1):
                    return False
                break
        else:
            return True


def main():
    totals = Counter()
    original = Counter()
    enhanced141 = Counter()
    enhanced130 = Counter()
    first_new = {}
    for heights in product(range(13), repeat=4):
        case = r2_case(*heights)
        if case is None:
            continue
        seeds = tuple(RAYS[col][row] for col, row in enumerate(heights))
        totals[case] += 1
        if propagate(seeds, ()):
            original[case] += 1
            if propagate(seeds, WINDOW141_CLAUSES):
                enhanced141[case] += 1
            if propagate(seeds, WINDOW141_CLAUSES + R2_CLAUSES):
                enhanced130[case] += 1
            else:
                first_new.setdefault(case, (heights, seeds))
    for case in ("H1", "H2", "H3"):
        print(case, "normalized tuples", totals[case],
              "survive prior propagation", original[case],
              "survive with 82 clauses", enhanced141[case],
              "survive with all 126 clauses", enhanced130[case],
              "first additional elimination", first_new.get(case))


if __name__ == "__main__":
    main()
