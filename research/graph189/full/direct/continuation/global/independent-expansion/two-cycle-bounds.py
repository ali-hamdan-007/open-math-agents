"""Enumerate necessary numerical conditions for a two-cycle cone factor.

The graph proof of these conditions is in cycle-splices.md.
"""


def possible_exterior(k, order, connectivity, exterior):
    gap = (k + 1) // 2 + 2
    path = order - exterior
    if exterior < gap or path < 2 * k + 1:
        return False

    arc_gap = max(0, gap + 1 - exterior // 2)
    contacts = max(0, k - exterior + 1)
    for groups in range(min(connectivity, exterior), path - 2 * gap + 1):
        marks = max(groups, contacts)
        if path < 2 * gap + marks + (groups - 1) * arc_gap:
            continue
        if groups >= exterior - 1:
            # The alternative where every high vertex has a singleton group.
            return True
        if groups < contacts:
            continue
        removed = groups - contacts + 1
        if (
            exterior - removed >= 2
            and 2 * k - 2 * groups - removed >= exterior + 1
        ):
            core_gap = max(arc_gap, gap - removed)
            if path < 2 * gap + marks + (groups - 1) * core_gap:
                continue
        return True
    return False


def least_exterior(k, order, connectivity):
    return next(
        (m for m in range((k + 1) // 2 + 2, order - 2 * k)
         if possible_exterior(k, order, connectivity, m)),
        None,
    )


if __name__ == "__main__":
    for k, order in [(11, 35), (13, 41), (26, 78), (26, 126), (26, 127),
                     (26, 130), (52, 260), (100, 500)]:
        for connectivity in (2, 3, 4):
            print(f"k={k} n={order} connectivity={connectivity} "
                  f"least_possible_exterior={least_exterior(k, order, connectivity)}")
