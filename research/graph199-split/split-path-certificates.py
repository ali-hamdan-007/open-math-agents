"""Generate or validate spanning-path certificates for the split residual."""

import argparse
import gzip
import importlib.util
import json
from functools import cache
from pathlib import Path

WORK = Path(__file__).resolve().parent
CERTIFICATES = WORK / "split-path-certificates.jsonl.gz"


def load_enumerator():
    spec = importlib.util.spec_from_file_location("residual", WORK / "check-split-residual.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def labels(groups, free):
    """List the stable-neighbor mask of each numbered clique vertex."""
    return [15, *free, *(mask | (1 << k)
                        for k, group in enumerate(groups, start=4) for mask in group)]


def path_is_valid(groups, free, path):
    rows = labels(groups, free)
    clique_size = len(rows)
    order = clique_size + 4 + len(groups)
    if not all(type(vertex) is int for vertex in path) or sorted(path) != list(range(order)):
        return False
    for u, v in zip(path, path[1:]):
        if u >= clique_size:
            u, v = v, u
        if v >= clique_size and (u >= clique_size or not (rows[u] & (1 << (v - clique_size)))):
            return False
    return True


def find_path(groups, free):
    rows = labels(groups, free)
    clique_size = len(rows)
    order = clique_size + 4 + len(groups)

    @cache
    def extend(last, remaining):
        if not remaining:
            return ()
        for nxt in remaining:
            u, v = sorted((last, nxt))
            if v >= clique_size and (u >= clique_size or not (rows[u] & (1 << (v - clique_size)))):
                continue
            suffix = extend(nxt, tuple(i for i in remaining if i != nxt))
            if suffix is not None:
                return (nxt, *suffix)
        return None

    vertices = (*range(clique_size, order), *range(clique_size))
    for first in vertices:
        suffix = extend(first, tuple(i for i in vertices if i != first))
        if suffix is not None:
            return [first, *suffix]
    raise ValueError(f"No spanning path for {(groups, free)!r}")


def generate():
    enumerator = load_enumerator()
    with CERTIFICATES.open("wb") as output, gzip.GzipFile(fileobj=output, mode="wb", mtime=0) as stream:
        def record(groups, free):
            path = find_path(groups, free)
            stream.write((json.dumps([groups, free, path], separators=(",", ":")) + "\n").encode())
            return True

        enumerator.traceable = record
        enumerator.main()


def check(coverage):
    paths = {}
    with gzip.open(CERTIFICATES, "rt", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            groups, free, path = json.loads(line)
            key = (tuple(map(tuple, groups)), tuple(free))
            if key in paths or not path_is_valid(*key, path):
                raise ValueError(f"Duplicate or invalid certificate at line {line_number}")
            paths[key] = path

    count = len(paths)
    if coverage:
        enumerator = load_enumerator()

        def require(groups, free):
            if paths.pop((groups, free), None) is None:
                raise ValueError(f"Missing certificate for {(groups, free)!r}")
            return True

        enumerator.traceable = require
        enumerator.main()
        if paths:
            raise ValueError(f"{len(paths)} certificates do not match an enumerated profile")
        print(f"Checked paths and enumeration coverage for {count} certificates.")
    else:
        print(f"Checked {count} explicit spanning paths.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["generate", "check", "coverage"])
    mode = parser.parse_args().mode
    if mode == "generate":
        generate()
    else:
        check(coverage=mode == "coverage")


if __name__ == "__main__":
    main()
