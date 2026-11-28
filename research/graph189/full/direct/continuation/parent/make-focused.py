"""Construct the focused version from the exact parent theorem binder text."""
import argparse
from pathlib import Path

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for field in ('assembled', 'registered', 'output'):
        p.add_argument(field, type=Path)
    p.add_argument('--modular-cut', action='store_true',
                   help='Import the verified cut-vertex modules when combining graph proofs.')
    args = p.parse_args()
    registered = args.registered.read_text()
    header = registered.split('theorem conjecture189 ', 1)[1].split(' := by', 1)[0]
    params, conclusion = header.split(') :\n', 1)
    statement = 'abbrev Graph189ParentAssembly.ExactStatement.{u} : Prop :=\n' + (
        '  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]\n    ' +
        params.replace('(h : G.Connected)', '(_ : G.Connected)').replace('(hσ : ', '(_ : ') +
        '),\n' + conclusion)
    src = args.assembled.read_text().replace(
        'import FormalConjectures.WrittenOnTheWallII.GraphConjecture189\n',
        'import Mathlib.Data.List.GetD\n'
        'import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees\n'
        'import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance\n')
    if args.modular_cut:
        start = src.index('section\n/-!\nThe parity estimate in Easwar–Johari')
        end = src.index('theorem Graph189ParentAssembly.cutVertex', start)
        src = 'import Graph189CutH1\n' + src[:start] + src[end:]
    target = 'type_of% @WrittenOnTheWallII.GraphConjecture189.conjecture189'
    assert src.count(target) == 2
    pre, body = src.split('/-!', 1)
    src = pre + 'open SimpleGraph in\n' + statement + '\n\n/-!' + body
    src = src.replace(target, 'Graph189ParentAssembly.ExactStatement.{u}')
    args.output.write_text(''.join((src, '\n#print axioms Graph189ParentAssembly.parent_of_two_connected_cases\n')))

if __name__ == '__main__':
    main()
