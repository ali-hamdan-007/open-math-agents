"""Generate exact integer constraints for a minimum four-cut population row."""

import argparse
import os
from pathlib import Path
import sys


ACTIVE = Path(__file__).resolve().parents[2]
LEASE_STATE = Path(os.environ.get("GRAPH189_LEASE_DIR", ACTIVE))
sys.path.insert(0, str(ACTIVE / "global" / "cut3"))
from exact_types import run_smt

MASKS = range(1, 16)
LABELS = range(4)


def plus(values):
    return "(+ 0 " + " ".join(values) + ")"


def either(values):
    return "(or false " + " ".join(values) + ")"


def contains(label, mask):
    return bool(mask & (1 << label))


def port(side, mask):
    return f"p{side}_{mask}"


def remote(side, mask):
    return f"r{side}_{mask}"


def contact(side, label):
    return f"c{side}_{label}"


def second(side, label):
    return f"s{side}_{label}"


def low_contact(side, label):
    return either(
        f"(= low{side} {mask})" for mask in MASKS if contains(label, mask)
    )


def live():
    return (LEASE_STATE / "LIVE").exists() and not any(
        (LEASE_STATE / mark).exists() for mark in ("PAUSE", "HALT")
    )


def build(k, populations, limit_a, limit_b, timeout, positive_control=False, full_a=None):
    """A low vertex may lie on a side; the separator's four vertices are high."""
    lines = [f"(set-option :timeout {timeout})", "(set-logic QF_LIA)"]

    def require(text):
        lines.append(f"(assert {text})")

    def natural(var, limit):
        lines.append(f"(declare-const {var} Int)")
        require(f"(and (<= 0 {var}) (<= {var} {limit}))")

    for side, population in enumerate(populations):
        natural(f"low{side}", 15)
        for mask in MASKS:
            natural(port(side, mask), population)
            natural(remote(side, mask), population)
        count = plus(v for mask in MASKS for v in (port(side, mask), remote(side, mask)))
        port_count = plus(port(side, mask) for mask in MASKS)
        require(f"(= {count} {population})")
        for label in LABELS:
            natural(contact(side, label), (limit_a, limit_b)[side])
            natural(second(side, label), k)
            natural(f"debit{side}_{label}", k * k)
            incident = plus(port(side, mask) for mask in MASKS if contains(label, mask))
            own = contact(side, label)
            other = second(side, label)
            require(f"(= {own} {incident})")
            remote_near = plus(remote(side, mask) for mask in MASKS if contains(label, mask))
            port_not_incident = plus(port(side, mask) for mask in MASKS if not contains(label, mask))
            require(f"(<= {remote_near} {other})")
            require(f"(<= {other} (+ {remote_near} {port_not_incident}))")
            require(f"(=> (> {own} {population - k + 3}) (= {other} (- {population} {own})))")
            require(f"(=> (> {own} 0) (>= {other} (- {k - 4} {own})))")
            require(f"(or (> {own} 0) {low_contact(side, label)})")
            require(f"(=> (= {own} 0) (and (= low{side} 15) (>= {other} {port_count})))")

    require("(or (= low0 0) (= low1 0))")
    for label in range(3):
        require(f"(>= {contact(0, label)} {contact(0, label + 1)})")
        require(
            f"(=> (= {contact(0, label)} {contact(0, label + 1)}) "
            f"(>= {contact(1, label)} {contact(1, label + 1)}))"
        )
    if full_a is not None:
        for label in LABELS:
            relation = "=" if label < full_a else "<"
            require(f"({relation} {contact(0, label)} {limit_a})")

    for side in (0, 1):
        opp = 1 - side
        for mask in MASKS:
            shared = plus(port(opp, other) for other in MASKS if mask & other)
            far = plus(remote(opp, other) for other in MASKS if not mask & other)
            budget = k - 4 + mask.bit_count()
            require(f"(=> (> {port(side, mask)} 0) (<= (+ {shared} {far}) {budget}))")
            require(f"(=> (= low{side} {mask}) (<= {shared} {budget}))")
            opposite_even = plus(
                [remote(opp, other) for other in MASKS]
                + [port(opp, other) for other in MASKS if not mask & other]
            )
            require(f"(=> (> {remote(side, mask)} 0) (<= {opposite_even} {k - 4}))")
            possible_neighbors = plus(
                [remote(side, other) for other in MASKS]
                + [port(side, other) for other in MASKS if other & mask == other]
            )
            require(f"(=> (> {remote(side, mask)} 0) (>= {possible_neighbors} {k}))")
            for label in LABELS:
                if not contains(label, mask):
                    continue
                candidates = [
                    other for other in MASKS if contains(label, other) and other & mask == other
                ]
                predecessor = either(
                    f"(or (> {port(side, other)} 0) (= low{side} {other}))"
                    for other in candidates
                )
                require(f"(=> (> {remote(side, mask)} 0) {predecessor})")

    for label in LABELS:
        require(f"(<= (+ {second(0, label)} {second(1, label)}) {k})")
        low0 = f"(ite {low_contact(0, label)} 1 0)"
        low1 = f"(ite {low_contact(1, label)} 1 0)"
        require(f"(>= (+ {contact(0, label)} {contact(1, label)} {low0} {low1}) {k - 3})")
        for side, maximum in ((0, limit_a), (1, limit_b)):
            coefficient = contact(side, label)
            count = second(1 - side, label)
            product = f"debit{side}_{label}"
            for v in range(maximum + 1):
                require(f"(=> (= {coefficient} {v}) (= {product} (* {v} {count})))")

    left, right = populations
    for side in (0, 1):
        ports = plus(contact(side, label) for label in LABELS)
        odd = plus(f"debit{s}_{label}" for s in (0, 1) for label in LABELS)
        require(f"(<= {left * right} (+ {populations[side] * (k - 4)} {ports} {odd}))")
    if positive_control:
        for side, population in enumerate(populations):
            require(f"(= {port(side, 15)} {population})")
            require(f"(= low{side} 0)")
            for label in LABELS:
                require(f"(= {second(side, label)} 0)")
    lines.append("(check-sat)")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("x", type=int)
    parser.add_argument("y", type=int)
    parser.add_argument("--a-max", type=int)
    parser.add_argument("--b-max", type=int)
    parser.add_argument("--timeout", type=int, default=20000)
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--positive-control", action="store_true")
    parser.add_argument("--full-a", type=int, choices=range(5))
    args = parser.parse_args()
    if not live():
        raise SystemExit("Graph 189 paused")
    if min(args.x, args.y) <= args.k and not args.positive_control:
        raise SystemExit("Each high population must exceed k for the nonport masks.")
    if args.positive_control and (args.x != args.k - 3 or args.y != args.k - 3):
        raise SystemExit("The positive control uses two cliques of order k-3.")
    formula = build(
        args.k,
        (args.x, args.y),
        args.k if args.a_max is None else args.a_max,
        args.k if args.b_max is None else args.b_max,
        args.timeout,
        args.positive_control,
        args.full_a,
    )
    if args.emit:
        print(formula)
    else:
        print(args.k, args.x, args.y, run_smt(formula), flush=True)


if __name__ == "__main__":
    main()
