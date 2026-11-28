"""Export checked relabeling witnesses for the exterior graph search."""
import argparse
from importlib.util import module_from_spec, spec_from_file_location
from itertools import permutations
from pathlib import Path


HERE = Path(__file__).resolve().parent
SEARCH = HERE.parent.parent / "root" / "moderate_exterior_search.py"


def edge_mask(rows, order):
    return sum(
        1 << (j * (j - 1) // 2 + i)
        for j, v in enumerate(order)
        for i, u in enumerate(order[:j])
        if rows[u] & (1 << v)
    )


def lean_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def generate(last):
    spec = spec_from_file_location("moderate_exterior_search", SEARCH)
    search = module_from_spec(spec)
    spec.loader.exec_module(search)
    print("""import Graph189ExteriorRelabel

namespace Graph189ExteriorMask

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The sole representative at order zero. -/
def reps0 : List ℕ := [0]

theorem covers0 : Covers 0 reps0 := covers_zero
""")
    previous = [0]
    for b, rows_list in search.graph_orders(last):
        identity = tuple(range(b))
        reps = [edge_mask(rows, identity) for rows in rows_list]
        # Use the search's canonical key only to select a target to check.
        # Each target requires an explicit adjacency-preserving permutation.
        by_key = {search.canonical(rows): (rows, mask)
                  for rows, mask in zip(rows_list, reps, strict=True)}
        print(f"def reps{b} : List ℕ := {lean_list(reps)}")
        print(f"def witnesses{b} : List RelabelWitness := [")
        previous_rows = (rows_before if b > 1 else [()])
        for old_rows, m in zip(previous_rows, previous, strict=True):
            for star in range(1 << (b - 1)):
                source_rows = tuple(row | (((star >> i) & 1) << (b - 1))
                                    for i, row in enumerate(old_rows)) + (star,)
                source = m + (1 << ((b - 1) * (b - 2) // 2)) * star
                target_rows, target = by_key[search.canonical(source_rows)]
                image = next(p for p in permutations(identity)
                             if edge_mask(target_rows, p) == source)
                print(f"  ⟨{source},{target},{lean_list(image)}⟩"
                      + ("," if (m, star) != (previous[-1], (1 << (b - 1)) - 1) else ""))
        print("]")
        print(f"""theorem covers{b} : Covers {b} reps{b} :=
  covers_succ covers{b-1} (by decide) (ws := witnesses{b})
    (by decide) (by decide)
""")
        check_rows = lean_list(lean_list(rows) for rows in rows_list)
        print(f"""theorem rows{b} : reps{b}.map (rowMasks {b}) = {check_rows} := by decide
""")
        previous, rows_before = reps, rows_list
    print("end Graph189ExteriorMask")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("last", type=int)
    generate(parser.parse_args().last)
