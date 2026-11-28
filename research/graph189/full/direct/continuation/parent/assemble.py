"""Build the conditional parent from the three identified, unmodified source files."""
import argparse
import hashlib
from pathlib import Path

TARGET = 'WrittenOnTheWallII.GraphConjecture189.conjecture189'
R2 = 'OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2'
CHILD = R2 + '_H2_R1'
IMPORT = 'import FormalConjectures.WrittenOnTheWallII.GraphConjecture189'
HASHES = [
    '5c5b95a2df5bb7925351320090bf5375bd06b7f32593e568e20ab30a1fa1cc64',
    '6a8ec853732119dd87acdc0b33620eaa4a8540a5cdd362a3398c1d202bd34ead',
    'd06e932f3e7703c9ed437a6b13aa5c22c732ef700a49e5002e9646bebb766477',
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('r2', 'cut', 'child', 'output'):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    imports = [IMPORT]
    bodies = []
    for index, path in enumerate((args.r2, args.cut, args.child)):
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != HASHES[index]:
            raise ValueError(f'{path} does not match the documented source')
        lines = raw.decode().splitlines()
        while lines and lines[0].startswith('import '):
            line = lines.pop(0)
            if line.startswith('import Mathlib.') and line not in imports:
                imports.append(line)
            elif not (line.startswith('import Mathlib.') or
                      line.startswith('import OMAReductions.') or line == IMPORT):
                raise ValueError(f'unrecognized import {line}')
        body = '\n'.join(lines).strip()
        if index == 1:
            old = 'theorem OMA.solution : ' + R2 + '.H1'
            if body.count(old) != 1:
                raise ValueError('missing original cut-vertex theorem')
            body = body.replace(old, 'theorem Graph189ParentAssembly.cutVertex : '+R2+'.H1')
        bodies.append(body)
    footer = f"""namespace Graph189ParentAssembly

theorem parent_of_two_connected_cases
    (moderate : {CHILD}.H1)
    (large : {CHILD}.H2) :
    type_of% @{TARGET} := by
  exact {R2}.main cutVertex ({CHILD}.main moderate large)

end Graph189ParentAssembly
"""
    doc = '/-!\nResearch assembly for WOW II 189. The final theorem assumes the two remaining cases.\nThe cut-vertex case is included. This file is a conditional research theorem.\n-/'
    args.output.write_text('\n'.join(imports)+'\n\n'+doc+'\n\n'+'\n\n'.join(bodies)+'\n\n'+footer)

if __name__ == '__main__':
    main()
