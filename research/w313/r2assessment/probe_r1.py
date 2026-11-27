"""Bounded SAT probes for the exact four proposed R1.H2.R1 hypotheses."""
from argparse import ArgumentParser
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

parser = ArgumentParser(description=__doc__)
parser.add_argument("cadical", type=Path)
parser.add_argument("--seconds", type=int, default=15)
parser.add_argument("--learned", action="store_true", help="add shifted and reflected checked seed clauses")
parser.add_argument("--lrat-size", action="store_true", help="measure H2/H3 binary LRAT via a pipe")
args = parser.parse_args()
solver = args.cadical.resolve()
cases = {
    "H1": (158, (75,), tuple(range(76, 82))),
    "H2": (159, (0, 77), tuple(range(78, 82))),
    "H3": (159, (76, 158), tuple(range(77, 81))),
    "H4": (160, (77,), (0, 159, *range(78, 82))),
}

WINDOWS = (
    (154, (1, 3, 13, 15)), (150, (14, 16, 26, 28)),
    (137, (27, 29, 39, 41)), (130, (64, 66, 76, 78)),
    (141, (43, 47, 48, 75)), (141, (73, 77, 78, 105)),
    (160, (66, 70, 71, 98)), (145, (0, 2, 14, 16)),
    (145, (24, 26, 38, 40)), (147, (52, 54, 66, 68)),
)


def learned_clauses(size):
    patterns = set()
    for width, seed in WINDOWS:
        for shift in range(size - width + 1):
            shifted = tuple(shift + x for x in seed)
            patterns.add(shifted)
            patterns.add(tuple(size - 1 - x for x in reversed(shifted)))
    return [tuple(-1 - x for x in pattern) for pattern in sorted(patterns)]

with TemporaryDirectory() as temp:
    for name, (size, red, blue) in cases.items():
        if args.lrat_size and name not in ("H2", "H3"):
            continue
        clauses = []
        for length, sign in ((3, -1), (13, 1)):
            for d in range(1, (size - 1) // (length - 1) + 1):
                for a in range(size - (length - 1) * d):
                    clauses.append(tuple(sign * (a + d * k + 1) for k in range(length)))
        clauses += [(p + 1,) for p in red] + [(-(p + 1),) for p in blue]
        if args.learned:
            clauses.extend(learned_clauses(size))
        cnf = Path(temp) / "case.cnf"
        with cnf.open("w") as out:
            print(f"p cnf {size} {len(clauses)}", file=out)
            for clause in clauses:
                print(*clause, 0, file=out)
        cmd = [str(solver), "-n", "-t", str(args.seconds)]
        if args.lrat_size:
            fifo = Path(temp) / "proof.fifo"
            os.mkfifo(fifo)
            reader = subprocess.Popen(["bash", "-c", 'wc -c < "$1"', "reader", str(fifo)],
                                      stdout=subprocess.PIPE, text=True)
            cmd += ["--lrat", "--binary", str(cnf), str(fifo)]
        else:
            cmd += [str(cnf)]
        run = subprocess.run(cmd, capture_output=True, text=True)
        status = next((line for line in run.stdout.splitlines() if line.startswith("s ")), "no status")
        stats = [line for line in run.stdout.splitlines() if line.startswith("c total process time")]
        if args.lrat_size:
            size, _ = reader.communicate(timeout=5)
            fifo.unlink()
            print(name, status, "exit", run.returncode, "LRAT bytes", size.strip(), *stats, flush=True)
        else:
            print(name, size, red, blue, status, "exit", run.returncode, *stats, flush=True)
