"""Count reusable local seed certificates for normalized nonalternating R2.H3."""
from collections import Counter, defaultdict
from itertools import product

N = 160


def normalized_nonalternating():
    for i, j, k, l in product(range(13), repeat=4):
        if (i != k or j != l) and i + k < 2*j and 2*k < j+l:
            if (i+l, j+k) <= (12, 12):
                yield i, j, k, l


def seed(heights):
    return tuple(sorted(13*h + r for r, h in enumerate(heights)))


def reflect(points):
    return tuple(N - 1 - x for x in reversed(points))


def offsets(points):
    return tuple(x - points[0] for x in points)


def anchors(points, shape, width):
    for placed in (points, reflect(points)):
        if offsets(placed) == shape:
            lo = max(0, placed[0] - (N - width))
            hi = min(placed[0], width - 1 - shape[-1])
            yield from range(lo, hi + 1)


groups = defaultdict(list)
for heights in normalized_nonalternating():
    points = seed(heights)
    groups[min(offsets(points), offsets(reflect(points)))].append(points)

assert sum(map(len, groups.values())) == 4882
print("Reflection-translation shapes:", len(groups))
print("Shape size histogram:", dict(sorted(Counter(map(len, groups.values())).items())))
for width in (145, 147, 150, 153, 159, 160):
    cover_counts = []
    full_sizes = []
    individual = 0
    for shape, placements in groups.items():
        covers = Counter()
        for points in placements:
            possible = set(anchors(points, shape, width))
            individual += bool(possible)
            covers.update(possible)
            for anchor in possible:
                local = tuple(anchor + x for x in shape)
                origin = points if offsets(points) == shape and points[0] - anchor in range(N-width+1) else reflect(points)
                start = origin[0] - anchor
                assert 0 <= start <= N-width and all(0 <= x < width for x in local)
                assert tuple(start + x for x in local) == origin
        largest = max(covers.values(), default=0)
        cover_counts.append(largest)
        if largest == len(placements):
            full_sizes.append(largest)
    print(width, "individual fits", individual, "largest single certificate", max(cover_counts),
          "fully covered shapes", len(full_sizes), "tuples in those shapes", sum(full_sizes),
          "cap with one certificate per shape", sum(cover_counts))
