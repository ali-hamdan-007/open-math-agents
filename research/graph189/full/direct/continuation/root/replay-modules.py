"""Replay selected Graph 189 research modules against an already built pinned project."""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CONTINUATION = HERE.parent
FOLDERS = ("root", "order", "verify", "lowblock", "global/arity/final",
           "verify/matched-formal", "sep/cover/final82/lean",
           "sep/cover/final82/lean/upstream", "parent")
LOCAL_IMPORT = re.compile(r"^import\s+(Graph189[A-Za-z0-9_]+)\s*(?:--.*)?$", re.MULTILINE)


def build_order(targets, extra):
    directories = [CONTINUATION / d for d in FOLDERS] + extra
    order = {}
    pending = set()

    def visit(name):
        if name in order:
            return
        if name in pending:
            raise ValueError(f"cyclic dependency at {name}")
        matches = [d / f"{name}.lean" for d in directories if (d / f"{name}.lean").is_file()]
        if not matches:
            raise ValueError(f"missing source for {name}; use --source-dir for earlier fork modules")
        data = matches[0].read_bytes()
        if any(p.read_bytes() != data for p in matches[1:]):
            raise ValueError(f"conflicting versions of {name}: {matches}")
        pending.add(name)
        for dependency in LOCAL_IMPORT.findall(data.decode("utf-8")):
            visit(dependency)
        pending.remove(name)
        order[name] = matches[0]

    for target in targets:
        visit(target)
    return order


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("modules", nargs="+")
    args.add_argument("--project", type=Path, help="Pinned formal-conjectures project (or set OMA_FC)")
    args.add_argument("--source-dir", type=Path, action="append", default=[])
    args.add_argument("--list", action="store_true", help="Only print the dependency order")
    args.add_argument("--lake-env", action="store_true", help=argparse.SUPPRESS)
    opt = args.parse_args()
    order = build_order(opt.modules, [p.resolve() for p in opt.source_dir])
    if opt.list:
        for p in order.values():
            print(p)
        return
    if not opt.lake_env:
        project = opt.project or os.environ.get("OMA_FC")
        if not project:
            args.error("--project or OMA_FC is required for compilation")
        options = [arg for p in opt.source_dir for arg in ("--source-dir", str(p.resolve()))]
        subprocess.run(["lake", "env", sys.executable, str(Path(__file__).resolve()),
                        "--lake-env", *options, *opt.modules], cwd=project, check=True)
        return
    # Lake can supply relative paths. Resolve them while still inside the project.
    paths = [str(Path(p).resolve()) for p in os.environ.get("LEAN_PATH", "").split(os.pathsep) if p]
    with tempfile.TemporaryDirectory(prefix="graph189-lean-") as tmp:
        env = {**os.environ, "LEAN_PATH": os.pathsep.join([tmp, *paths])}
        subprocess.run(["lean", "--version"], env=env, check=True)
        for name, source in order.items():
            shutil.copyfile(source, Path(tmp) / source.name)
            subprocess.run(["lean", "-j1", "-DwarningAsError=true", "-o", name + ".olean",
                            source.name], env=env, cwd=tmp, check=True)


if __name__ == "__main__":
    main()
