"""Reproduce the focused Graph 189 import from @koolkao's accepted OMA PR 7971.

Use the exact single-file proof and a pinned formal-conjectures checkout.
The linked-set theorem and its dependencies are copied without editing.
"""
import argparse
import hashlib
from pathlib import Path

BLOB = "1094243524b455ea5dace0862e4c6ec05a7ed312"
IMPORTS = """import Graph189LinkedExterior
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Lattice.Nat
"""


def part(source, first, after):
    begin = source.index(first)
    return source[begin:source.index(after, begin)]


def read_body(checkout, source):
    circumference = (checkout / "FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean").read_text()
    bondy = (checkout / "FormalConjectures/Arxiv/2606.03696/BondyLongestCycles.lean").read_text()
    return (IMPORTS + "\n" + part(circumference, "namespace SimpleGraph", "end SimpleGraph")
            + "end SimpleGraph\n\nopen SimpleGraph\n" + part(bondy, "namespace Arxiv.", "/--\n**Conjecture 1")
            + "end Arxiv.«2606.03696»\n\n" + part(source, "namespace OMA.BondyK", "end linked")
            + "end linked\n\n" + part(source,"section glue", "open Arxiv.«2606.03696» in")
            + "end glue\nend OMA.BondyK\n\n#print axioms OMA.BondyK.linked_contra\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path)
    parser.add_argument("formal_conjectures", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    data = args.proof.read_bytes()
    prefix = f"blob {len(data)}\0".encode()
    if hashlib.sha1(prefix + data).hexdigest() != BLOB:
        raise SystemExit("The upstream proof's Git blob differs from the recorded accepted input.")
    args.destination.write_text(read_body(args.formal_conjectures, data.decode()))


if __name__ == "__main__":
    main()
