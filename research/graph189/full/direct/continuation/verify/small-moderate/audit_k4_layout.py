"""Check which necessary layout conditions are sufficient for exact k=4 coverage."""
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
SEARCH = HERE.parent.parent / "root" / "moderate_exterior_search.py"
KEYS = HERE.parent / "moderate-certs" / "patterns-4.json"

spec = spec_from_file_location("moderate_exterior_search", SEARCH)
search = module_from_spec(spec)
spec.loader.exec_module(search)
catalogue = {(r["p"], tuple(r["ext"]), tuple(r["contacts"]))
             for r in json.loads(KEYS.read_text())}

found = set()
by_order = Counter()
local_rows = Counter()
spaced_rows = Counter()
prefix_nodes = Counter()
k = 4
for b, graphs in search.graph_orders(6):
    if b < 3:
        continue
    for exterior in graphs:
        length = search.path_lengths(exterior)
        degrees = [row.bit_count() for row in exterior]
        for p in range(7, 14-b):
            candidates = []
            for x, degree in enumerate(degrees):
                margin = max(length[x])
                choices = []
                for cardinality in range(max(0,k-1-degree), p-2*margin+1):
                    for positions in combinations(range(margin,p-margin),cardinality):
                        if all(j>=i+2 for i,j in zip(positions,positions[1:])):
                            choices.append(sum(1 << i for i in positions))
                candidates.append(choices)
            count = 1
            for choices in candidates:
                count *= len(choices)
            local_rows[p,b] += count
            assigned = [0] * b
            order = sorted(range(b), key=lambda i: len(candidates[i]))

            def prefix_even(active):
                forced = {x: assigned[x].bit_count()+degrees[x]+1 == k for x in active}
                for x in active:
                    contacts = assigned[x]
                    reached = search.positions(contacts,1)
                    for y in search.bits(exterior[x]):
                        if y in forced:
                            reached |= assigned[y]
                    path_two = (reached & ~contacts & ((1 << p)-1)).bit_count()
                    peer_two = sum(y!=x and not (exterior[x] & (1 << y)) and (
                        bool(contacts & assigned[y] or exterior[x] & exterior[y]) or forced[x] and forced[y])
                        for y in active)
                    if path_two+peer_two > k:
                        return False
                return True

            def finish():
                spaced_rows[p,b] += 1
                if any(not any(assigned[y] for y in range(b) if length[x][y])
                       for x in range(b)):
                    return
                forced = [assigned[x].bit_count()+degrees[x]+1 == k for x in range(b)]
                for x, contacts in enumerate(assigned):
                    reached = search.positions(contacts,1)
                    for y in search.bits(exterior[x]):
                        reached |= assigned[y]
                    path_two = (reached & ~contacts & ((1 << p)-1)).bit_count()
                    peer_two = sum(y!=x and not (exterior[x] & (1 << y)) and (
                        bool(contacts & assigned[y] or exterior[x] & exterior[y]) or forced[x] and forced[y])
                        for y in range(b))
                    if path_two+peer_two > k:
                        return
                by_order[p,b] += 1
                found.add((p, exterior,tuple(assigned)))

            def assign(level):
                if level == b:
                    finish()
                    return
                x = order[level]
                for mask in candidates[x]:
                    if all(not mask & search.positions(assigned[y],length[x][y]) for y in order[:level]):
                        assigned[x] = mask
                        if prefix_even(order[:level+1]):
                            prefix_nodes[p,b] += 1
                            assign(level+1)

            assign(0)

for p,b in sorted(local_rows):
    print(p,b,local_rows[p,b],prefix_nodes[p,b],spaced_rows[p,b],by_order[p,b])
print("found",len(found),"catalogue",len(catalogue),"extra",len(found-catalogue),"missed",len(catalogue-found))
for row in sorted(found-catalogue)[:12]:
    print("extra", row)

assert found == catalogue
