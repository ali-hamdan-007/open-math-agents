"""Generate a narrower instance of the existing bit-mask checker."""
from argparse import ArgumentParser
from pathlib import Path
import re
import subprocess

work = Path(__file__).resolve().parent
root = work.parent
parser = ArgumentParser(description=__doc__)
parser.add_argument("offset", type=int, nargs="?", default=73)
parser.add_argument("--width", type=int, default=141)
parser.add_argument("--shape", default="0,4,5,32", help="comma-separated red offsets")
args = parser.parse_args()
width, offset = args.width, args.offset
shape = sorted(set(map(int, args.shape.split(","))))
if not 13 <= width <= 160 or min(shape) != 0 or not 0 <= offset < width - max(shape):
    parser.error("the seed must fit inside a window of length 13 through 160")
points = [offset + i for i in shape]
seed = "".join("1" if p in points else "?" for p in range(offset, points[-1] + 1))
module = f"Green{width}Window"

source = (root / "Green160NearWitness.lean").read_text()
start = source.index("namespace OMA.Green160NearWitness")
end = source.index("set_option maxRecDepth 10000 in", source.index("theorem certify"))
checker = source[start:end].replace("OMA.Green160NearWitness", f"OMA.{module}")
checker = checker.replace("< 160", f"< {width}")
(work / f"{module}Core.lean").write_text(
    "import Lean\n\n"
    f"/-! The sound Green160NearWitness checker instantiated on {width} points. "
    "Instruction offsets use the existing fixed stride of 160. -/\n\n"
    + checker + f"\nend OMA.{module}\n"
)

run = subprocess.run(
    [str(root / "search160"), seed, str(width), str(offset), "emit"],
    capture_output=True, text=True, check=True,
)
summary = re.search(r"^sat=0, calls=(\d+), depth=(\d+), lemmas=(\d+)", run.stderr, re.M)
if summary is None:
    raise ValueError(f"No contradiction certificate: {run.stderr}")
tape = re.sub(r"\blemma (v\d+)", r"private theorem \1", run.stdout)
last = re.findall(r"^private theorem (v\d+) : Bad \([^\n]*?,(0x[\da-f]+)\)", tape, re.M)[-1]
tail = (work / "window.tail").read_text()
for marker, value in {
    "@WIDTH@": str(width), "@SHIFT@": str(160 - width),
    "@LAST@": last[0], "@MASK@": last[1],
    "@ORDERED@": str(points), "@REVERSED@": str(list(reversed(points))),
    "@CASES@": " ∨ ".join(f"x = {p}" for p in reversed(points)),
    "@POINTS@": " | ".join("rfl" for _ in points),
}.items():
    tail = tail.replace(marker, value)
namespace = f"OMA.{module}.Seed{offset}"
(work / f"{module}{offset}.lean").write_text(
    f"import {module}Core\nimport Green160NearWitness\n\nnamespace {namespace}\n\n"
    + tape + "\n" + tail +
    f"\nend {namespace}\n\n"
    f"#print axioms {namespace}.shifted_forces_progression\n"
    f"#print axioms {namespace}.reflected_shifted_forces_progression\n"
)
print(run.stderr.strip())
