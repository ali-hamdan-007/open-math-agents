"""Replay research theorems using the active pinned Lean and mathlib environment."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("formal_conjectures", type=Path)
    parser.add_argument("build", type=Path)
    parser.add_argument("targets", nargs="+")
    args = parser.parse_args()
    fc = args.formal_conjectures.resolve()
    build = args.build.resolve()
    build.mkdir(parents=True, exist_ok=True)
    verify = Path(__file__).resolve().parent
    graph = verify.parents[3]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(build), env.get("LEAN_PATH", "")])
    files = {}
    for source in sorted(graph.rglob("*.lean"), key=lambda p: (
        "continuation" not in p.parts, "verify" not in p.parts, len(p.parts), str(p)
    )):
        files.setdefault(source.stem, source)
    for source in sorted(graph.parent.glob("*.lean")):
        files.setdefault(source.stem, source)
    focused = build / "Graph189ParentFocused.lean"
    parent = verify.parent / "parent"
    subprocess.run([
        sys.executable, str(parent / "make-focused.py"), str(parent / "Graph189ParentAssembly.lean"),
        str(fc / "FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean"), str(focused)
    ], check=True)
    files[focused.stem] = focused
    imports = re.compile(r"^(?:public\s+)?import\s+(\w+(?:\.\w+)*)", re.M)
    signatures = {}

    def compile_module(name):
        if name in signatures:
            return signatures[name]
        relative = Path(*name.split(".")).with_suffix(".lean")
        source = fc / relative if name.startswith("FormalConjectures") else files[name]
        data = source.read_bytes()
        digest = hashlib.sha256(data)
        for dep in imports.findall(data.decode()):
            if dep.startswith(("FormalConjectures", "Graph189")):
                digest.update(compile_module(dep).encode())
        signature = digest.hexdigest()
        local = build / relative
        compiled = local.with_suffix(".olean")
        stamp = local.with_suffix(".sha")
        if not (compiled.is_file() and stamp.is_file() and stamp.read_text() == signature):
            local.parent.mkdir(parents=True, exist_ok=True)
            local.write_bytes(data)
            print(f"Checking {name}", flush=True)
            check = subprocess.run(["lean", "-j1", "-o", str(compiled), str(local)], env=env,
                                   cwd=build, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            local.with_suffix(".log").write_text(check.stdout)
            if check.returncode or "sorryAx" in check.stdout or "uses 'sorry'" in check.stdout:
                raise SystemExit(check.stdout or check.returncode)
            stamp.write_text(signature)
        signatures[name] = signature
        return signature

    for target in args.targets:
        compile_module(target)
        print((build / target).with_suffix(".log").read_text(), end="")


if __name__ == "__main__":
    main()
