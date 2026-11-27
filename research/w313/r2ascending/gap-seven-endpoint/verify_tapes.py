#!/usr/bin/env python3
"""Independently check the regenerated width-159 certificate using sets."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import re

if not __debug__:
    raise SystemExit("Run this verifier without Python optimization.")

parser = ArgumentParser(description=__doc__)
parser.add_argument('source_dir', type=Path, help='Directory containing the regenerated dag.json and Lean sources')
root = parser.parse_args().source_dir.resolve()
width = 159
universe = frozenset(range(width))
pattern = re.compile(
    r'theorem v(\d+) : Bad \(\[([0-9,]*)\],0x([0-9a-f]+)\) :='
    r' certify 0x1((?:[0-9a-f]{4})*) #\[(.*)\] \(by decide \+kernel\)'
)
gate_pattern = re.compile(r'⟨_,v(\d+)⟩')
fragments = {}
for module in json.loads((root / 'dag.json').read_text()):
    for line in (root / f'{module}.lean').read_text().splitlines():
        if not line.startswith('theorem v'):
            continue
        fragment, red, possible, tape, gates = pattern.fullmatch(line).groups()
        fragment = int(fragment)
        assert fragment not in fragments, fragment
        red = tuple(map(int, red.split(',')))
        possible = int(possible, 16)
        assert possible.bit_length() <= width
        allowed = frozenset(x for x in universe if (possible >> x) & 1)
        ops = tuple(reversed([int(tape[i:i+4], 16) for i in range(0, len(tape), 4)]))
        references = gate_pattern.findall(gates)
        assert ','.join(f'⟨_,v{reference}⟩' for reference in references) == gates
        gates = tuple(map(int, references))
        fragments[fragment] = (red, allowed, ops, gates)


def prohibited_thirds(p, q):
    if p == q:
        return set()
    banned = {2*p-q, 2*q-p}
    if (p+q) % 2 == 0:
        banned.add((p+q)//2)
    return banned


def restrict(allowed, red, p):
    return allowed.difference(*(prohibited_thirds(p, q) for q in red))


operations = Counter()
maximum_depth = 0
for fragment in range(len(fragments)):
    start_red, start_allowed, ops, gates = fragments[fragment]
    assert all(g < fragment for g in gates)

    def visit(index, red, allowed, depth):
        global maximum_depth
        assert index < len(ops) and depth <= 60, (fragment, index, depth)
        maximum_depth = max(maximum_depth, depth)
        op = ops[index]
        if op >= 3000:
            operations['gates'] += 1
            link_red, link_allowed, _, _ = fragments[gates[op - 3000]]
            assert (red, allowed) == (link_red, link_allowed), (fragment, index, op)
            return index + 1
        if op >= 256:
            d, a = divmod(op - 256, 160)
            assert 1 <= d <= 13 and a + 12*d < width, (fragment, index, a, d)
            remaining = allowed.intersection(a + t*d for t in range(13))
            if not remaining:
                operations['empty progressions'] += 1
                return index + 1
            assert len(remaining) == 1, (fragment, index, remaining)
            operations['forced red positions'] += 1
            p = next(iter(remaining))
            return visit(index + 1, (p, *red), restrict(allowed, red, p), depth + 1)
        assert op in allowed and op not in red, (fragment, index, op)
        operations['two-way splits'] += 1
        next_index = visit(index + 1, (op, *red), restrict(allowed, red, op), depth + 1)
        return visit(next_index, red, allowed.difference({op}), depth + 1)

    assert visit(0, start_red, start_allowed, 1) == len(ops), fragment

red, allowed, _, _ = fragments[len(fragments)-1]
assert red == (94, 92, 2, 0)
assert allowed == universe.difference(*(prohibited_thirds(p, q) for p, q in combinations(red, 2)))
assert len(fragments) == 927
print(f'Checked every operation in all {len(fragments)} topologically indexed certificate fragments')
print(f'Maximum depth within any fragment: {maximum_depth}')
print(f'Operation counts: {dict(sorted(operations.items()))}')
print('Root seed and its allowed positions match width 159 and [0, 2, 92, 94]')
