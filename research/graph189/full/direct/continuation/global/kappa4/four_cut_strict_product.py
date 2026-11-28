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


if __name__ == "__main__":
    main()
