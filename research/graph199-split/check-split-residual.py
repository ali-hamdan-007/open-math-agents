"""Exhaust split profiles with a four-vertex core and at most three outsiders."""

from collections import Counter
from functools import cache
from itertools import combinations_with_replacement

GROUP_ROWS = tuple(row for row in range(16) if 2 <= row.bit_count() <= 3)
BASE_GROUPS = tuple(group for group in combinations_with_replacement(GROUP_ROWS, 3)
                    if all((a ^ b).bit_count() <= 3 for a in group for b in group))


def compatible(group, other):
    return all((a ^ b).bit_count() <= 1 for a in group for b in other)


def base_profiles(count, groups=(), start=0):
    if not count:
        yield groups
        return
    for i in range(start, len(BASE_GROUPS)):
        group = BASE_GROUPS[i]
        if all(compatible(group, other) for other in groups):
            yield from base_profiles(count - 1, groups + (group,), i)


def traceable(groups, free):
    rows = [15, *free]
    for label, group in enumerate(groups, 4):
        rows.extend(row | (1 << label) for row in group)
    n_clique = len(rows)
    n = n_clique + 4 + len(groups)
    clique = (1 << n_clique) - 1
    neighbors = [(clique ^ (1 << i)) | (row << n_clique) for i, row in enumerate(rows)]
    neighbors.extend(sum(1 << i for i, row in enumerate(rows) if row & (1 << k))
                     for k in range(n - n_clique))
    all_vertices = (1 << n) - 1

    @cache
    def extend(end, remaining):
        if not remaining:
            return True
        options = neighbors[end] & remaining
        while options:
            preferred = options & ~clique or options
            pick = preferred & -preferred
            options ^= pick
            if extend(pick.bit_length() - 1, remaining ^ pick):
                return True
        return False

    return any(extend(i, all_vertices ^ (1 << i))
               for i in (*range(n_clique, n), *range(n_clique)))


def main():
    for count in range(1, 4):
        stats = Counter()

        @cache
        def visit(groups, free):
            stats['profile visits'] += 1
            bits = [1 << i for i in range(4)]
            group_rows = tuple(row for group in groups for row in group)
            needed = next((bit for bit in bits
                           if sum(bool(row & bit) for row in (*group_rows, *free)) < 2), None)
            if needed is None:
                stats['Hamiltonian tests'] += 1
                if not traceable(groups, free):
                    raise SystemExit(f'Nontraceable profile: {groups=}, {free=}')
                if 1 + len(free) + len(group_rows) >= 4 + count:
                    return
            for row in range(1, 16):
                if needed is not None and not row & needed:
                    continue
                if all((row ^ other).bit_count() <= 3 for other in free) and all(
                    (row ^ other).bit_count() <= 2 for other in group_rows
                ):
                    visit(groups, tuple(sorted((*free, row))))
                if row not in GROUP_ROWS:
                    continue
                for j, group in enumerate(groups):
                    if not all((row ^ other).bit_count() <= 3 for other in group):
                        continue
                    if not all(compatible((row,), other) for i, other in enumerate(groups) if i != j):
                        continue
                    if not all((row ^ other).bit_count() <= 2 for other in free):
                        continue
                    replacement = tuple(sorted((*group, row)))
                    visit(tuple(sorted((*groups[:j], replacement, *groups[j + 1 :]))), free)

        for groups in base_profiles(count):
            stats['base profiles'] += 1
            visit(groups, ())
        print(count, dict(stats), flush=True)


if __name__ == '__main__':
    main()
