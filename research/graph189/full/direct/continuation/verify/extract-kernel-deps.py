"""Extract the custom declaration dependencies from a completed pinned Lean build."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

IMPORT = re.compile(r"^(?:public\s+)?import\s+(?:all\s+)?(Graph189\w+)", re.M)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("build", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--root", default="Graph189ModerateComplete.moderate")
args = parser.parse_args()
build = args.build.resolve()
names = set()

def visit(module):
    if module in names:
        return
    names.add(module)
    for dep in IMPORT.findall((build / (module + ".lean")).read_text()):
        visit(dep)

visit(args.root.partition(".")[0])
driver = Path(__file__).with_suffix(".lean").read_text()
with tempfile.TemporaryDirectory() as tmp:
    src = Path(tmp) / "DependencyAudit.lean"
    src.write_text("".join(f"import {n}\n" for n in sorted(names)) + driver)
    subprocess.run(["lean", "-j1", str(src)], check=True, env={
        **os.environ, "LEAN_PATH": os.pathsep.join([str(build), os.environ.get("LEAN_PATH", "")]),
        "GRAPH189_ROOT": args.root, "GRAPH189_DEPENDENCIES": str(args.output.resolve())})
print(f"{sum(1 for _ in args.output.open())} kernel declarations across {len(names)} transitive modules")
