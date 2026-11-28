"""Replay the seven distinct contact-mask rows at second degree 29."""

from pathlib import Path
import subprocess
import sys

from four_cut_masks import live


ROWS = [(36, 114), (37, 113), (38, 112), (39, 111), (41, 109), (37, 114), (38, 113)]


def run(args):
    script = Path(__file__).with_name("four_cut_masks.py")
    process = subprocess.Popen(
        [sys.executable, str(script), *map(str, args)], stdout=subprocess.PIPE, text=True
    )
    try:
        while live():
            try:
                output, _ = process.communicate(timeout=0.25)
            except subprocess.TimeoutExpired:
                continue
            if process.returncode:
                raise SystemExit(process.returncode)
            return output.strip().rsplit(" ", 1)[-1]
        raise SystemExit("Graph 189 paused")
    finally:
        if process.poll() is None:
            process.terminate()
            process.wait()


def main():
    limits = ["--a-max", 28, "--b-max", 27]
    positive = run([29, 26, 26, *limits, "--positive-control"])
    assert positive == "sat"
    print("positive", positive, flush=True)
    unresolved = []
    for x, y in ROWS:
        for full in range(5):
            result = run([29, x, y, *limits, "--full-a", full, "--timeout", 15000])
            print(x, y, full, result, flush=True)
            if result != "unsat":
                unresolved.append((x, y, full, result))
    print("remaining", unresolved, flush=True)


if __name__ == "__main__":
    main()
