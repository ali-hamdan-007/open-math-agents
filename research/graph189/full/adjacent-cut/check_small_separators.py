"""Check the small-parameter cases in shallow-adjacent.md, using Python 3.10+.

Credit: gpt-6.2-astra. No third-party packages are needed.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
import sys

COMMON, P_ONLY, Q_ONLY, INTERIOR = 3, 1, 2, 0


def port_profiles(count):
    # Permuting vertices with identical roles preserves every condition below.
    for common in range(1, count + 1):
        for p_only in range(count - common + 1):
            q_only = count - common - p_only
            yield (COMMON,) * common + (P_ONLY,) * p_only + (Q_ONLY,) * q_only


def spanning_path(adj, endpoints):
    full = (1 << len(adj)) - 1
    for start in range(len(adj)):
        @lru_cache(None)
        def extend(last, used):
            if used == full:
                return endpoints(start, last)
            available = adj[last] & ~used
            while available:
                bit = available & -available
                available -= bit
                if extend(bit.bit_length() - 1, used | bit):
                    return True
            return False

        if extend(start, 1 << start):
            return True
    return False


def graphs_for_side(k, roles, low, opposite, is_large_side):
    """Return (number of admissible graphs, first path failure, if any)."""
    order = len(roles)
    port_count_opposite = sum(role != INTERIOR for role in opposite)
    compulsory = [0] * order
    optional = []
    for left, right in combinations(range(order), 2):
        incident_to_common = COMMON in (roles[left], roles[right])
        if is_large_side:
            # Common C ports become universal inside C via ordinary path closure.
            degree_sum = 2*k - (roles[left] != INTERIOR) - (roles[right] != INTERIOR)
            forced = incident_to_common or (low not in (left, right) and degree_sum >= order)
        else:
            # A D common port with k C ports opposite uses its entire even budget.
            forced = incident_to_common and port_count_opposite == k
        if forced:
            compulsory[left] |= 1 << right
            compulsory[right] |= 1 << left
        else:
            optional.append((left, right))

    internal_minimum = [(3 if v == low else k) - role.bit_count()
                        for v, role in enumerate(roles)]
    outside_witnesses = [sum(bool(role & other) for other in opposite)
                         + (role in (P_ONLY, Q_ONLY)) for role in roles]
    shared_anchor = [sum(1 << u for u, other in enumerate(roles)
                         if u != v and role & other)
                     for v, role in enumerate(roles)]

    count = 0
    failure = None
    for mask in range(1 << len(optional)):
        adj = compulsory.copy()
        while mask:
            bit = mask & -mask
            mask -= bit
            left, right = optional[bit.bit_length() - 1]
            adj[left] |= 1 << right
            adj[right] |= 1 << left
        if any(neighbors.bit_count() < required
               for neighbors, required in zip(adj, internal_minimum)):
            continue
        if any(outside_witnesses[v] + (shared_anchor[v] & ~adj[v]).bit_count() > k
               for v in range(order)):
            continue
        count += 1
        if is_large_side:
            augmented = adj + [0]
            for v, role in enumerate(roles):
                if role == COMMON:
                    augmented[v] |= 1 << order
                    augmented[order] |= 1 << v
            found = spanning_path(augmented, lambda first, last: True)
        else:
            def assign_anchors(first, last):
                return bool((roles[first] & P_ONLY and roles[last] & Q_ONLY)
                            or (roles[first] & Q_ONLY and roles[last] & P_ONLY))
            found = spanning_path(adj, assign_anchors)
        if not found:
            failure = tuple(adj)
            break
    return count, failure


def possible_low_vertices(k, large, shallow, shallow_nonports):
    if shallow_nonports:
        if k > 3:
            yield None, len(shallow) - 1
        return
    yield None, None  # no low vertex in either component, including a low anchor
    if k == 3:
        return
    for role in sorted(set(large) - {COMMON}):
        yield large.index(role), None
    for role in sorted(set(shallow)):
        yield None, shallow.index(role)


def verify(k):
    totals = Counter()
    for a in range(1, k + 1):
        for b in (k - 1, k):
            for t in range(k + 1):
                for w in (0, 1):
                    if 2 + a + t + b + w <= 3*k:
                        continue
                    for ports_c in port_profiles(a):
                        for ports_d in port_profiles(b):
                            large = ports_c + (INTERIOR,)*t
                            shallow = ports_d + (INTERIOR,)*w
                            p_only = large.count(P_ONLY) + shallow.count(P_ONLY)
                            q_only = large.count(Q_ONLY) + shallow.count(Q_ONLY)
                            if max(p_only, q_only) > k-t+(b < k):
                                continue
                            if t == k and min(p_only, q_only) > 0:
                                continue
                            for lc, ld in possible_low_vertices(k, large, shallow, w):
                                if len(shallow) == k-1 and any(
                                    role != COMMON and v != ld
                                    for v, role in enumerate(shallow)
                                ):
                                    continue
                                d_count, d_failure = graphs_for_side(k, shallow, ld, large, False)
                                if not d_count:
                                    continue
                                c_count, c_failure = graphs_for_side(k, large, lc, shallow, True)
                                if not c_count:
                                    continue
                                if c_failure is not None or d_failure is not None:
                                    raise RuntimeError((k, large, shallow, lc, ld, c_failure, d_failure))
                                totals["profiles"] += 1
                                totals["C instances"] += c_count
                                totals["D instances"] += d_count
    return totals["profiles"], totals["C instances"], totals["D instances"]


if __name__ == "__main__":
    degrees = [int(arg) for arg in sys.argv[1:]] or [3, 4, 5]
    for degree in degrees:
        if degree not in (3, 4, 5):
            raise ValueError("The finite check applies at k = 3, 4, 5.")
        print(degree, *verify(degree), flush=True)
