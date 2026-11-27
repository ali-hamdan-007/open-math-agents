"""Generate the width-154 edge certificate in bounded Lean modules."""
from argparse import ArgumentParser
from pathlib import Path
import re
import subprocess

work = Path(__file__).resolve().parent
ramsey = work.parent.parent
parser = ArgumentParser(description=__doc__)
parser.add_argument("solver", type=Path)
args = parser.parse_args()

source = (ramsey / "Green160NearWitness.lean").read_text()
start = source.index("namespace OMA.Green160NearWitness")
end = source.index("set_option maxRecDepth 10000 in", source.index("theorem certify"))
checker = source[start:end].replace("OMA.Green160NearWitness", "OMA.Green154Edge")
checker = checker.replace("< 160", "< 154")
(work / "Green154EdgeCore.lean").write_text(
    "import Lean\n\n" + checker + "\nend OMA.Green154Edge\n"
)

search = subprocess.run([str(args.solver.resolve()), "1?1?????????1?1", "154", "1", "emit"],
                        capture_output=True, text=True, check=True)
if not re.search(r"^sat=0, calls=", search.stderr, re.M):
    raise ValueError(f"No certificate: {search.stderr}")

blocks = re.split(r"(?=^set_option maxRecDepth)", search.stdout, flags=re.M)
blocks = [block for block in blocks if block]
chunks = []
size = 0
for i, block in enumerate(blocks):
    if re.search(r"^lemma v(\d+) :", block, re.M).group(1) != str(i):
        raise ValueError("Unexpected theorem order")
    if any(int(dep) >= i for dep in re.findall(r"⟨_,v(\d+)⟩", block)):
        raise ValueError("Dependency is not earlier than its consumer")
    if not chunks or size + len(block.encode("utf-8")) > 76 * 1024:
        chunks.append([])
        size = 0
    chunks[-1].append(block.replace(f"lemma v{i} :", f"theorem v{i} :"))
    size += len(block.encode("utf-8"))
if not blocks:
    raise ValueError("Empty certificate")

previous = "Green154EdgeCore"
for i, chunk in enumerate(chunks):
    name = f"Green154EdgeChunk{i:02}"
    (work / f"{name}.lean").write_text(
        f"import {previous}\n\nnamespace OMA.Green154Edge\n\n"
        + "".join(chunk) + "\nend OMA.Green154Edge\n"
    )
    previous = name

last = re.search(r"^lemma (v\d+) : Bad \([^\n]*?,(0x[\da-f]+)\)", blocks[-1], re.M)
tail = (work.parent / "window.tail").read_text()
markers = {
    "@WIDTH@": "154", "@SHIFT@": "6", "@LAST@": last[1], "@MASK@": last[2],
    "@ORDERED@": "[1, 3, 13, 15]", "@REVERSED@": "[15, 13, 3, 1]",
    "@CASES@": "x = 15 ∨ x = 13 ∨ x = 3 ∨ x = 1",
    "@POINTS@": "rfl | rfl | rfl | rfl",
}
for marker, value in markers.items():
    tail = tail.replace(marker, value)
(work / "Green154EdgeSeed.lean").write_text(
    f"import {previous}\nimport Green160NearWitness\n\nnamespace OMA.Green154Edge\n\n"
    + tail + "\nend OMA.Green154Edge\n\n"
    "#print axioms OMA.Green154Edge.shifted_forces_progression\n"
    "#print axioms OMA.Green154Edge.reflected_shifted_forces_progression\n"
)
(work / "search.log").write_text(search.stderr + f"chunks={len(chunks)}\n")
print(search.stderr, end="")
print(f"Generated {len(chunks)} bounded certificate modules.")
