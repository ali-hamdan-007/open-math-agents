"""Classify R2 ray fibers reached by affine transport of the checked windows."""

from collections import Counter

SIZE = 160
WINDOWS = (
    (154, (1, 3, 13, 15)),
    (150, (14, 16, 26, 28)),
    (137, (27, 29, 39, 41)),
    (130, (64, 66, 76, 78)),
    (141, (43, 47, 48, 75)),
    (141, (73, 77, 78, 105)),
    (160, (66, 70, 71, 98)),
)


def embeddings(width, seed):
    for step in range(1, (SIZE - 1) // (width - 1) + 1):
        last_start = SIZE - 1 - step * (width - 1)
        for start in range(last_start + 1):
            forward = tuple(start + step * x for x in seed)
            yield forward
            yield tuple(sorted(SIZE - 1 - x for x in forward))


def rays(seed):
    heights = {}
    for x in seed:
        height, residue = divmod(x, 13)
        if residue > 3 or residue in heights:
            return None
        heights[residue] = height
    return tuple(heights[r] for r in range(4))


def normalized_case(heights):
    i, j, k, l = heights
    first = i + k - 2 * j
    second = j + l - 2 * k
    earlier = (i + l, j + k) <= (12, 12)
    if first > 0 and second > 0:
        return "H1"
    if first > 0 and second < 0 and earlier:
        return "H2"
    if first < 0 and second > 0 and earlier:
        return "H3"
    return "unnormalized"


def main():
    patterns = set()
    for width, seed in WINDOWS:
        images = set(embeddings(width, seed))
        patterns |= images
        print(width, seed, "patterns", len(images), "ray fits",
              sum(rays(image) is not None for image in images))
    fibers = sorted({heights for pattern in patterns if (heights := rays(pattern)) is not None})
    symmetric_starts = [a for a, b, c, d in sorted(patterns) if (b-a, c-a, d-a) == (2, 12, 14)]
    categories = Counter(normalized_case(heights) for heights in fibers)
    print("Distinct forbidden patterns:", len(patterns))
    print("Distinct symmetric starts:", len(symmetric_starts))
    print("Ray fibers:", fibers)
    print("Counts:", dict(categories))
    assert fibers == [(h+1, h, h+1, h) for h in range(12)]
    assert categories == {"H2": 6, "unnormalized": 6}


if __name__ == "__main__":
    main()
