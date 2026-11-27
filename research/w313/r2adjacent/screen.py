"""Reproduce bounded searches for normalized alternating R2-H2 tuples."""
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from itertools import product
from pathlib import Path
import re
import subprocess


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, default=Path(__file__).resolve().parents[1] / "search160")
    parser.add_argument("--windows", action="store_true", help="try window widths 125 through 160 for adjacent tuples")
    parser.add_argument("--edge", action="store_true", help="test only the edge tuple at selected widths")
    args = parser.parse_args()
    solver = args.solver.resolve()

    def run(job):
        i, j, width = job
        start = 13 * j + 1
        offsets = {0, 2, 13 * (i - j) - 1, 13 * (i - j) + 1}
        if start + max(offsets) >= width:
            return i, j, width, "seed outside window"
        seed = "".join("1" if p in offsets else "?" for p in range(max(offsets) + 1))
        try:
            result = subprocess.run([str(solver), seed, str(width), str(start)],
                                    capture_output=True, text=True, timeout=2)
        except subprocess.TimeoutExpired:
            return i, j, width, "timeout"
        match = re.search(r"sat=(\d+), calls=(\d+)", result.stderr)
        status = f"sat={match[1]} nodes={match[2]}" if match else result.stderr.strip()
        if args.windows and (not match or match[1] != "0"):
            return None
        return i, j, width, status

    if args.edge:
        jobs = [(1, 0, n) for n in (152, 154, 160)]
    elif args.windows:
        jobs = [(h + 1, h, n) for h, n in product(range(6), range(125, 161))]
    else:
        jobs = [(i, j, 160) for i in range(13) for j in range(i) if i + j <= 12]
    with ThreadPoolExecutor(max_workers=4) as executor:
        for result in executor.map(run, jobs):
            if result is not None:
                print(*result)


if __name__ == "__main__":
    main()
