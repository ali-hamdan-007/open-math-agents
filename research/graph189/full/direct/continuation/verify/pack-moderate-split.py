"""Generate the official moderate child reduction and its four exact leaf proof files."""
import argparse
from pathlib import Path
import subprocess
import sys

STEP = "WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1.H1"
MODULE = "OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("build",type=Path)
parser.add_argument("directory",type=Path)
parser.add_argument("--dependencies", type=Path, help="directory with short.tsv, five.tsv, six.tsv and seven.tsv")
parser.add_argument("--checkout-sources",action="store_true")
args = parser.parse_args()
verify = Path(__file__).resolve().parent
reductions = args.directory/"reductions"
proofs = args.directory/"proofs"
reductions.mkdir(parents=True,exist_ok=True)
proofs.mkdir(parents=True,exist_ok=True)
reports=args.directory/"reports"
reports.mkdir(parents=True,exist_ok=True)
source=(verify/"Graph189ModerateSplit.lean").read_text()
assert source.startswith("import Graph189ParentFocused\n")
(reductions/(STEP+".R1.lean")).write_text(source.replace("import Graph189ParentFocused", "import "+MODULE,1))
for i, name in enumerate(("short","five","six","seven"),1):
    target = proofs/(STEP+f".R1.H{i}.lean")
    command = [sys.executable, str(verify/"pack-moderate.py"), str(args.build),str(target),"--leaf",str(i)]
    if args.dependencies:
        command.extend(["--dependencies",str(args.dependencies/(name+".tsv"))])
    if args.checkout_sources:
        command.append("--checkout-sources")
    subprocess.run(command, check=True)
    report=target.with_suffix(".modules.tsv")
    report.replace(reports/report.name)
