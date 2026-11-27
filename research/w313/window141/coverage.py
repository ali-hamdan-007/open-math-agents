"""Export checked red-set clauses or count their exact uniform coverage."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations
from math import prod


def clause_sets(specs, include_old, r2_starts=()):
    clauses = {
        frozenset((start + i, start + i + 4, start + i + 5, start + i + 32))
        for start, count in specs for i in range(count)
    }
    clauses |= {frozenset(159 - i for i in clause) for clause in clauses}
    if include_old:
        clauses.update((frozenset((66, 70, 71, 98)), frozenset((61, 88, 89, 93))))
    clauses.update(frozenset((x, x + 2, x + 12, x + 14)) for x in r2_starts)
    return clauses


def choose_variable(factors, variables):
    adjacent = {v: set() for v in variables}
    for scope, _ in factors:
        for vertex in scope:
            adjacent[vertex].update(w for w in scope if w != vertex)

    def cost(vertex):
        neighbors = adjacent[vertex]
        fill = sum(w not in adjacent[u] for u, w in combinations(neighbors, 2))
        return fill, len(neighbors), vertex

    return min(variables, key=cost)


def projection(positions, width):
    """Map each assignment index in the combined scope to a local index."""
    indices = [0]
    positions = {pos: i for i, pos in enumerate(positions)}
    for i in range(width):
        bit = 1 << positions[i] if i in positions else 0
        indices += [p | bit for p in indices]
    return indices


def coverage(clauses):
    variables = set().union(*clauses)
    total = 1 << len(variables)
    # Each 4-clause factor accepts every assignment except all four red.
    factors = [(tuple(sorted(clause)), [1] * 15 + [0]) for clause in clauses]
    while variables:
        vertex = choose_variable(factors, variables)
        uses = [(s, f) for s, f in factors if vertex in s]
        factors = [(s, f) for s, f in factors if vertex not in s]
        neighbors = sorted(set().union(*(s for s, _ in uses)) - {vertex})
        width = len(neighbors)
        if width > 20:
            raise ValueError("Counting scope too wide; choose fewer offsets.")
        positions = {point: i for i, point in enumerate(neighbors)}
        tables = []
        for scope, values in uses:
            i = scope.index(vertex)
            compressed = projection([positions[p] for p in scope if p != vertex], width)
            indices = [(a & ((1 << i) - 1)) | ((a >> i) << (i + 1)) for a in compressed]
            tables.append((indices, values, 1 << i))
        merged = []
        for assignment in range(1 << width):
            blue = red = 1
            for indices, values, bit in tables:
                blue *= values[indices[assignment]]
                red *= values[indices[assignment] | bit]
            merged.append(blue + red)
        factors.append((tuple(neighbors), merged))
        variables.remove(vertex)
    return 1 - Fraction(prod(f[0] for _, f in factors), total)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("windows", metavar="START:COUNT", nargs="*")
    parser.add_argument("--old", action="store_true", help="include both prior four-red clauses")
    parser.add_argument("--dimacs", action="store_true", help="output only the added clauses")
    parser.add_argument("--r2", metavar="LOW:HIGH", help="include R2-shaped starts in an inclusive interval")
    args = parser.parse_args()
    specs = [tuple(map(int, s.split(":"))) for s in args.windows] or [(73, 20)]
    if any(start not in (43, 73) or not 1 <= count <= 20 for start, count in specs):
        parser.error("certified starts are 43 and 73, with between 1 and 20 offsets")
    if args.r2:
        lo, hi = map(int, args.r2.split(":"))
        if not 51 <= lo <= hi <= 94:
            parser.error("R2-shaped start interval must lie in [51,94]")
        r2_starts = range(lo, hi + 1)
    else:
        r2_starts = ()
    clauses = clause_sets(specs if args.windows or not args.r2 else (), args.old, r2_starts)
    if args.dimacs:
        print(f"p cnf 160 {len(clauses)}")
        for clause in sorted(tuple(sorted(clause)) for clause in clauses):
            print(*(str(-(x + 1)) for x in clause), 0)
    else:
        ratio = coverage(clauses)
        print(f"{len(clauses)} clauses: {ratio} ({float(ratio):.12%})")


if __name__ == "__main__":
    main()
