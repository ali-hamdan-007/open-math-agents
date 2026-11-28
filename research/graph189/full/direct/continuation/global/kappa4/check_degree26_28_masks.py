"""Replay the remaining unrestricted four-cut mask rows."""

import argparse
from pathlib import Path

from check_degree29_masks import run
from four_cut_strict_product import unresolved_rows


def populations(k):
    """Keep pairs unexcluded by the refined one-common and debited product arguments."""
    pairs = set()
    rows = 0
    for _, x, y, slack in unresolved_rows(k):
        private_quota = 4 * (4 * k - 11 + x) + x < 4 * (x + y)
        if y >= 4 * k - 1 and private_quota:
            continue
        if slack < max(0, 4 * (x - k)):
            continue
        if x > k and y > 4 * k - 7 and y > 9 * k - 4 * x - 4 and slack < 4 * x:
            continue
        rows += 1
        pairs.add((x, y))
    return rows, sorted(pairs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--degrees", type=int, nargs="+", choices=range(24, 29), default=[26, 27, 28])
    args = parser.parse_args()
    completed = set()
    controls = set()
    if args.resume:
        for line in args.resume.read_text().splitlines():
            pieces = line.split()
            if len(pieces) == 5 and pieces[-1] == "unsat":
                completed.add(tuple(map(int, pieces[:4])))
            if len(pieces) == 3 and pieces[1:] == ["positive", "sat"]:
                controls.add(int(pieces[0]))
    remaining = []
    expected_rows = {24: 78, 25: 59, 26: 43, 27: 29, 28: 18}
    for k in args.degrees:
        if k not in controls:
            positive = run([k, k - 3, k - 3, "--positive-control"])
            assert positive == "sat"
            print(k, "positive", positive, flush=True)
        rows, pairs = populations(k)
        assert rows == expected_rows[k]
        assert all(x > k and y > k for x, y in pairs)
        print(k, "population rows", rows, "distinct pairs", len(pairs), flush=True)
        for x, y in pairs:
            for full in range(5):
                if (k, x, y, full) in completed:
                    continue
                result = run([k, x, y, "--full-a", full, "--timeout", 12000])
                print(k, x, y, full, result, flush=True)
                if result != "unsat":
                    remaining.append((k, x, y, full, result))
    print("remaining", remaining, flush=True)


if __name__ == "__main__":
    main()
