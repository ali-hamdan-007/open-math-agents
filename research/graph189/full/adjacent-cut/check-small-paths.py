"""Independent forward subset-DP replacement for the checker's path search."""
from pathlib import Path
from importlib.util import module_from_spec, spec_from_file_location
spec = spec_from_file_location("separators", Path(__file__).with_name('check_small_separators.py'))
checker = module_from_spec(spec)
spec.loader.exec_module(checker)
def check_path(adj, acceptable):
    n = len(adj)
    full = 2**n - 1
    for start in range(n):
        end_mask = sum(1 << v for v in range(n) if acceptable(start, v) and v != start)
        if not end_mask:
            continue
        reachable = [0] * (1 << n)
        reachable[1 << start] = 1 << start
        for mask, ends in enumerate(reachable):
            while ends:
                last = ends & -ends
                ends -= last
                available = adj[last.bit_length()-1] & ~mask
                while available:
                    nxt = available & -available
                    available -= nxt
                    reachable[mask | nxt] |= nxt
            if reachable[full] & end_mask:
                return True
    return False
checker.spanning_path = check_path
for k in (3,4,5):
    print(k, checker.verify(k), flush=True)
