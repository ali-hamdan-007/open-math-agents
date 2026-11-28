"""Exact integer necessary conditions for the row (k,x,y) = (31,38,124)."""

import argparse
from pathlib import Path
import sys


ACTIVE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ACTIVE / "global" / "cut3"))
from exact_types import run_smt

K = 31
N = (38, 124)
MASKS = range(1, 16)
LABELS = range(4)


def plus(values):
    return "(+ 0 " + " ".join(values) + ")"


def disjunction(values):
    return "(or false " + " ".join(values) + ")"


def conjunction(values):
    return "(and true " + " ".join(values) + ")"


def port(side, mask):
    return f"p{side}_{mask}"


def remote(side, mask):
    return f"r{side}_{mask}"


def contact(side, label):
    return f"c{side}_{label}"


def second(side, label):
    return f"s{side}_{label}"


def variables(side):
    for mask in MASKS:
        yield port(side, mask)
        yield remote(side, mask)
    for label in LABELS:
        yield contact(side, label)
        yield second(side, label)
        yield f"debit{side}_{label}"


def contains(label, mask):
    return bool(mask & (1 << label))


def live():
    return (ACTIVE / "LIVE").exists() and not any(
        (ACTIVE / mark).exists() for mark in ("PAUSE", "HALT")
    )


def build(full, timeout, populations=N, positive_control=False):
    lines = [f"(set-option :timeout {timeout})", "(set-logic QF_LIA)"]

    def require(text):
        lines.append(f"(assert {text})")

    for side, population in enumerate(populations):
        for var in variables(side):
            lines.append(f"(declare-const {var} Int)")
            require(f"(>= {var} 0)")
        low = f"low{side}"
        lines.append(f"(declare-const {low} Int)")
        require(f"(and (<= 0 {low}) (<= {low} 15))")
        count = plus(v for mask in MASKS for v in (port(side, mask), remote(side, mask)))
        require(f"(= {count} {population})")
        for label in LABELS:
            incident = plus(port(side, mask) for mask in MASKS if contains(label, mask))
            own = contact(side, label)
            require(f"(= {own} {incident})")
            require(f"(<= {own} {30 if side == 0 else 29})")
            other = second(side, label)
            remote_near = plus(remote(side, mask) for mask in MASKS if contains(label, mask))
            port_not_incident = plus(port(side, mask) for mask in MASKS if not contains(label, mask))
            require(f"(<= {remote_near} {other})")
            require(f"(<= {other} (+ {remote_near} {port_not_incident}))")
            require(f"(<= {other} {K})")
            # Missing the label leaves at most three separator neighbors.
            # If it cannot avoid all high contacts internally, the distance is two.
            require(f"(=> (> {own} {population - K + 3}) (= {other} (- {population} {own})))")
            low_incident = disjunction(f"(= low{side} {mask})" for mask in MASKS if contains(label, mask))
            require(f"(or (> {own} 0) {low_incident})")

    require("(or (= low0 0) (= low1 0))")
    require(conjunction(f"(>= {contact(0, i)} {contact(0, i + 1)})" for i in range(3)))
    for i in LABELS:
        if i < full:
            require(f"(= {contact(0, i)} 30)")
        else:
            require(f"(<= {contact(0, i)} 29)")

    for side in (0, 1):
        opp = 1 - side
        for mask in MASKS:
            # Shared-label opposite ports are at distance two. Opposite high
            # nonports whose nearest-label sets are disjoint are at distance four.
            shared = plus(port(opp, other) for other in MASKS if mask & other)
            far = plus(remote(opp, other) for other in MASKS if not mask & other)
            budget = K - 4 + mask.bit_count()
            require(f"(=> (> {port(side, mask)} 0) (<= (+ {shared} {far}) {budget}))")
            require(f"(=> (= low{side} {mask}) (<= {shared} {budget}))")
            # In an opposite high pair with two nonports the distance is four.
            # The same is true for a port with no label in this nearest-label set.
            opposite_even = plus(
                [remote(opp, other) for other in MASKS]
                + [port(opp, other) for other in MASKS if not mask & other]
            )
            require(f"(=> (> {remote(side, mask)} 0) (<= {opposite_even} {K - 4}))")
            for label in LABELS:
                if not contains(label, mask):
                    continue
                # A shortest two-step path stays inside this side until the
                # cut. Its middle port touches only labels in the mask.
                candidates = [other for other in MASKS if contains(label, other) and other & mask == other]
                pred = disjunction(
                    f"(or (> {port(side, other)} 0) (= low{side} {other}))" for other in candidates
                )
                require(f"(=> (> {remote(side, mask)} 0) {pred})")

    for label in LABELS:
        require(f"(<= (+ {second(0, label)} {second(1, label)}) {K})")
        for side, maximum in ((0, 30), (1, 29)):
            coefficient = contact(side, label)
            count = second(1 - side, label)
            product = f"debit{side}_{label}"
            for v in range(maximum + 1):
                require(f"(=> (= {coefficient} {v}) (= {product} (* {v} {count})))")

    edge_coins = plus(
        [contact(0, label) for label in LABELS]
        + [f"debit{side}_{label}" for side in (0, 1) for label in LABELS]
    )
    left, right = populations
    require(f"(<= {left * right} (+ {left * (K - 4)} {edge_coins}))")
    if positive_control:
        # Two disjoint 28-cliques joined to four independent common anchors.
        # Each side vertex has degree 31 and exactly 28 positive even targets.
        # Each anchor has three positive even targets. The four anchors are
        # a minimum cut. These constraints specify its exact high-port profile.
        for side, population in enumerate(populations):
            require(f"(= {port(side, 15)} {population})")
            require(f"(= low{side} 0)")
            for label in LABELS:
                require(f"(= {second(side, label)} 0)")
    lines.append("(check-sat)")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("full", type=int, choices=(0, 1, 2))
    parser.add_argument("--timeout", type=int, default=15000)
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--positive-control", action="store_true")
    args = parser.parse_args()
    if not live():
        raise SystemExit("Graph 189 paused")
    formula = (
        build(0, args.timeout, (28, 28), True)
        if args.positive_control
        else build(args.full, args.timeout)
    )
    if args.emit:
        print(formula)
    else:
        print(args.full, run_smt(formula), flush=True)


if __name__ == "__main__":
    main()
