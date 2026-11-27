"""Ordinary and hypothetical cyclic width-147 coverage of the 55 endpoints.

The ordinary maximum is 0: each set includes 0 and 159. For cyclic
transport, order the four points around Z/160Z and record their four gaps.
Translation rotates the gap tuple and reflection reverses it up to rotation.
The longest gap is at least 40, so cutting at that gap gives span <=120.
Consequently every endpoint fits a cyclic width-147 window. The pairwise
distinct dihedral gap tuples below imply a hypothetical maximum of 1.

This shape argument cannot transport ordinary AP avoidance. In the cyclic
window starting at 159, the first three positions pull back to 159, 0, 1
and the first thirteen pull back to 159, 0, ..., 11. Neither is an
ordinary AP in [0,160). A partial coloring of that exact wrapped window
shows the resulting failure without requiring any color for the omitted
points. Other verified examples show that cyclic rotation of a valid ordinary coloring can create both
a green 3-AP and a red 13-AP. Colorings use zero-based indices.
"""


def cyclic_shape(points, ambient_width):
    gaps = tuple(
        (following - current) % ambient_width
        for current, following in zip(points, points[1:] + points[:1])
    )
    return min(
        order[shift:] + order[:shift]
        for order in (gaps, gaps[::-1])
        for shift in range(4)
    )


def arithmetic_progressions(domain, length):
    last = max(domain)
    for first in sorted(domain):
        for step in range(1, (last - first) // (length - 1) + 1):
            progression = {first + index * step for index in range(length)}
            if progression <= domain:
                yield progression


def verify_avoidance(domain, green):
    assert green <= domain
    assert not any(ap <= green for ap in arithmetic_progressions(domain, 3))
    red = domain - green
    assert not any(ap <= red for ap in arithmetic_progressions(domain, 13))


def verify_rotation(width, green, start, green_ap, red_ap):
    # This is rotation modulo width, not the map from [0,160).
    domain = set(range(width))
    verify_avoidance(domain, green)
    rotated_green = {(point - start) % width for point in green}
    assert green_ap <= rotated_green
    assert green_ap in arithmetic_progressions(domain, 3)
    assert red_ap <= domain - rotated_green
    assert red_ap in arithmetic_progressions(domain, 13)


def main():
    ambient_width = 160
    window_width = 147
    endpoints = [
        tuple(sorted((0, 13 * j + 1, 13 * k + 2, 159)))
        for j in range(13)
        for k in range(13)
        if (j, k) != (12, 0) and k < 2 * j and 2 * k < j + 12 and j + k <= 12
    ]
    assert len(endpoints) == 55
    assert all(points[-1] - points[0] >= window_width for points in endpoints)
    shapes = {cyclic_shape(points, ambient_width) for points in endpoints}
    assert len(shapes) == len(endpoints)
    assert all(ambient_width - max(gaps) < window_width for gaps in shapes)

    wrapped_points = [(159 + index) % ambient_width for index in range(window_width)]
    wrapped_domain = set(wrapped_points)
    wrapped_green = {
        0, 1, 8, 9, 13, 22, 29, 42, 47, 60, 61, 66, 68, 79,
        87, 88, 99, 104, 105, 118, 125, 126, 133, 139, 143, 159,
    }
    verify_avoidance(wrapped_domain, wrapped_green)
    assert set(wrapped_points[:3]) <= wrapped_green

    verify_rotation(
        147,
        {0, 1, 6, 14, 25, 26, 31, 32, 34, 45, 53, 57, 60,
         70, 77, 79, 91, 96, 99, 110, 117, 118, 130, 131, 136, 146},
        3,
        {143, 144, 145},
        set(range(14, 14 + 13 * 11, 11)),
    )
    verify_rotation(
        159,
        {12, 23, 25, 26, 39, 42, 43, 50, 54, 64, 67, 68, 73, 76, 81,
         90, 101, 106, 114, 115, 118, 128, 132, 133, 143, 156},
        13,
        {102, 130, 158},
        set(range(144, 157)),
    )
    print("55 endpoints. Ordinary maximum 0. Hypothetical cyclic maximum 1.")
    print("Ordinary avoidance and rotation counterexamples verified.")


if __name__ == "__main__":
    main()
