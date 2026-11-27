"""Exhaust the 21-vertex four-group profile left by the Hall argument."""

from functools import lru_cache
from itertools import combinations_with_replacement

CORE = range(4)
TYPES = [mask for mask in range(16) if 2 <= mask.bit_count() <= 3]
GROUPS = list(combinations_with_replacement(TYPES, 3))


def compatible(first, second):
    """Different outsider labels contribute two private stable neighbors."""
    return all((left ^ right).bit_count() <= 1 for left in first for right in second)


def profiles(prefix=(), first=0):
    if len(prefix) == 4:
        yield prefix
        return
    for index in range(first, len(GROUPS)):
        group = GROUPS[index]
        if all(compatible(group, earlier) for earlier in prefix):
            yield from profiles(prefix + (group,), index)


def hamiltonian_path(groups):
    clique_size = 13
    vertex_count = 21
    clique_mask = (1 << clique_size) - 1
    neighbors = [clique_mask ^ (1 << vertex) for vertex in range(clique_size)]
    neighbors.extend([0] * (vertex_count - clique_size))

    def edge(u, v):
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u

    for core in CORE:
        edge(0, clique_size + core)
    for group_id, group in enumerate(groups):
        for row, core_mask in enumerate(group):
            clique_vertex = 1 + 3 * group_id + row
            edge(clique_vertex, clique_size + 4 + group_id)
            for core in CORE:
                if core_mask & (1 << core):
                    edge(clique_vertex, clique_size + core)
    remaining_all = (1 << vertex_count) - 1

    @lru_cache(None)
    def extend(last, remaining):
        if remaining == 0:
            return True
        possible = neighbors[last] & remaining
        while possible:
            next_bit = possible & -possible
            possible ^= next_bit
            nxt = next_bit.bit_length() - 1
            if extend(nxt, remaining ^ next_bit):
                return True
        return False

    # A spanning path may start anywhere. Stable vertices first help the search.
    return any(extend(start, remaining_all ^ (1 << start))
               for start in list(range(clique_size, vertex_count)) + list(range(clique_size)))


def main():
    checked = 0
    for groups in profiles():
        if any(sum(bool(row & (1 << core)) for group in groups for row in group) < 2
               for core in CORE):
            continue
        checked += 1
        if not hamiltonian_path(groups):
            raise SystemExit(f"Counterexample to the tested profile: {groups}")
    print(f"Checked all {checked} profiles with stable minimum degree three.")


if __name__ == "__main__":
    main()
