"""Enumerate the finite gap left by the original four-cut population estimate."""


def unresolved_rows(k):
    for n in range(6 * k - 19, 6 * k - 10):
        for total in (n - 5, n - 4):
            for x in range(total // 2 + 1):
                y = total - x
                slack = k * x + 4 * k * k - x * y
                if slack < 0:
                    continue
                original = (
                    y > 4 * k
                    and n > 5 * k + 5
                    and 4 * (4 * k - 11 + x) + x < 4 * total
                    and 3 * (5 * k - 4) + k < 3 * total
                )
                if not original:
                    yield n, x, y, slack


def rejects(k, x, y, slack):
    return x > k and y > 4 * k - 4 and y > 9 * k - 4 * x and slack < 4 * x


def main():
    expected = {
        32: [(173, 40, 128), (173, 41, 127), (173, 44, 124), (173, 45, 123)],
        33: [(179, 42, 132)],
    }
    for k in range(32, 37):
        survivors = []
        for n, x, y, slack in unresolved_rows(k):
            excluded = rejects(k, x, y, slack)
            print(k, n, x, y, slack, "excluded" if excluded else "remaining")
            if not excluded:
                survivors.append((n, x, y))
        assert survivors == expected.get(k, [])
    degree31 = [
        (n, x, y, slack)
        for n, x, y, slack in unresolved_rows(31)
        if not rejects(31, x, y, slack) and slack >= max(0, 4 * (x - 31))
    ]
    assert degree31 == [
        (167, 38, 124, 310),
        (167, 39, 123, 256),
        (167, 40, 122, 204),
        (167, 42, 120, 106),
        (167, 43, 119, 60),
        (167, 39, 124, 217),
        (167, 40, 123, 164),
        (168, 39, 124, 217),
        (168, 40, 123, 164),
    ]
    for row in degree31:
        print(31, *row, "see the degree-31 proof")
    degree30 = []
    k = 30
    for n, x, y, slack in unresolved_rows(k):
        if y >= 4 * k - 1 and 4 * (4 * k - 11 + x) + x < 4 * (x + y):
            continue
        if slack < max(0, 4 * (x - k)):
            continue
        if x > k and y > 4 * k - 7 and y > 9 * k - 4 * x - 4 and slack < 4 * x:
            continue
        degree30.append((n, x, y, slack))
    assert degree30 == [
        (161, 38, 118, 256),
        (161, 39, 117, 207),
        (161, 40, 116, 160),
        (161, 39, 118, 168),
        (162, 39, 118, 168),
    ]
    for row in degree30:
        print(30, *row, "see the degree-30 proof")


if __name__ == "__main__":
    main()
