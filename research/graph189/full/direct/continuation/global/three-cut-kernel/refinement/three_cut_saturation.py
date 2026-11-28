"""Exact population tests for the three-cut saturation note."""


def saturation_impossible(source, target, k):
    """Three independently sufficient exclusions for a full source column."""
    return (
        target > 3 * k - 2
        or (source > 2 * k - 3 and target > 2 * k)
        or (target > k and source > 2 * k - 3 and source > 7 * k - 3 * target)
    )


def column_max(source, target, k):
    if target > 2 * k + 1:
        return k - 2
    if target > 2 * k or saturation_impossible(source, target, k):
        return k - 1
    return k


def charge(x, y, u, v, k):
    upper = k * x + 3 * u + 3 * k * max(u, v)
    if u < v and x > k:
        upper -= min(max(0, 3 * u - x), (v - u) * max(0, y - k - v))
    return upper


def residual_population(x, y, k):
    u = column_max(x, y, k)
    v = column_max(y, x, k)
    if x * (y + 3) > charge(x, y, u, v, k):
        return False
    if y * (x + 3) > charge(y, x, v, u, k):
        return False
    if y <= 3 * k:
        return True
    if 3 * y <= 9 * k - 15 + x:
        if x + 1 > 2 * k - 1 or 2 * x + 3 * y <= 12 * k - 12:
            return True
    return x <= u and 2 * y <= 6 * k + x


def frontier(k, n):
    # x<=y and the coarse product x*y<=kx+3k² imply x<3k.
    # A Y population above all three original quota thresholds is excluded.
    result = []
    for x in range(3 * k + 1):
        last_y = max(3 * k, (9 * k - 15 + x) // 3, (6 * k + x) // 2)
        for y in range(max(x, n - 4 - x), last_y + 1):
            if residual_population(x, y, k):
                result.append((x, y))
    return result


if __name__ == "__main__":
    for degree in range(20, 38):
        n = 5 * degree - 11
        survivors = frontier(degree, n)
        print(degree, n, survivors[:1], len(survivors))
        if degree >= 25:
            assert not survivors
    assert frontier(24, 109)[0] == (22, 83)
