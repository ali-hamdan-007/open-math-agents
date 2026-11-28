"""Search clique components behind a fixed cardinality cut, then verify witnesses."""

from collections import deque
from pathlib import Path
import random

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp


ROOT = Path(__file__).resolve().parents[1]
RNG = random.Random(18920261128)


def live():
    return (ROOT / "LIVE").exists() and not any(
        (ROOT / mark).exists() for mark in ("PAUSE", "HALT")
    )


def distances(neighbors, stop=None):
    n = len(neighbors)
    distance = np.full((n, n), n + 1, dtype=np.int16)
    for start in range(n):
        if start == stop:
            continue
        distance[start, start] = 0
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v in neighbors[u]:
                if v != stop and distance[start, v] == n + 1:
                    distance[start, v] = distance[start, u] + 1
                    queue.append(v)
    return distance


def template(s, centers, lobes):
    n = s + sum(map(len, lobes))
    neighbors = [set() for _ in range(n)]
    for u in range(s):
        for v in range(u):
            if centers >> (u * (u - 1) // 2 + v) & 1:
                neighbors[u].add(v)
                neighbors[v].add(u)
    start = s
    for masks in lobes:
        for v, mask in enumerate(masks, start):
            for u in range(start, v):
                neighbors[u].add(v)
                neighbors[v].add(u)
            for u in range(s):
                if mask >> u & 1:
                    neighbors[u].add(v)
                    neighbors[v].add(u)
        start += len(masks)
    return neighbors


def random_lobe(s, density):
    while True:
        count = RNG.choice([1, 2, 2, 2, 3, 3, 4])
        masks = {
            sum((1 << j) for j in range(s) if RNG.random() < density)
            for _ in range(count)
        }
        if len(masks) >= 2 and np.bitwise_or.reduce(list(masks)).bit_count() >= 2:
            return sorted(masks)


def random_center(s):
    while True:
        centers = RNG.randrange(1 << (s * (s - 1) // 2))
        neighbor = template(s, centers, [])
        degrees = [len(row) for row in neighbor]
        if 2 <= max(degrees) < s - 1:
            return centers


def score(s, centers, lobes, possible_low=None):
    neighbor = template(s, centers, lobes)
    n = len(neighbor)
    if any(sum(bool(set(range(sum(map(len, lobes[:i])) + s,
                              sum(map(len, lobes[:i + 1])) + s)) & neighbor[u])
               for i in range(len(lobes))) < 3 for u in range(s)):
        return None
    distance = distances(neighbor)
    high = [x for x in range(n) if x != possible_low]
    if distance.max() > 5 or distance[np.ix_(high, high)].max() > 4:
        return None
    closed = (distance <= 1).astype(float)
    even = ((distance == 2) | (distance == 4)).astype(float)
    e = np.c_[even, -np.ones(n), -np.ones(n)]
    d = np.c_[-closed[high], np.ones(len(high)), np.zeros(len(high))]
    active = [e, d, np.r_[-np.ones(n), 3, 0][None, :]]
    rhs = [np.zeros(n), -np.ones(len(high)), np.array([-3])]
    if possible_low is not None:
        active.append(np.r_[closed[possible_low], -1, 0][None, :])
        rhs.append(np.array([0]))
        active.append(np.r_[-closed[possible_low], 0, 0][None, :])
        rhs.append(np.array([-7]))
    start = s
    for group in lobes:
        one = np.zeros(n + 2)
        one[start:start + len(group)] = -1
        active.append(one[None, :])
        rhs.append(np.array([-3]))
        for v, u_mask in enumerate(group, start):
            if v != possible_low:
                min_k = u_mask.bit_count() + 2
                one = np.r_[np.zeros(n), -1, 0]
                active.append(one[None, :])
                rhs.append(np.array([-min_k]))
        start += len(group)
    A = np.vstack(active)
    B = np.concatenate(rhs)
    bounds = (
        [(1, 1)] * s
        + [(1, 1) if x == possible_low else (1, None) for x in range(s, n)]
        + [(6, 4 * (s - 1) - 1), (0, None)]
    )
    obj = np.r_[np.full(n, 0.00001), 0, 1]
    result = linprog(obj, A_ub=A, b_ub=B, bounds=bounds, method="highs")
    if not result.success:
        return None
    slack = result.x[-1]
    if slack > 1e-6:
        return slack, None
    lo = [b[0] for b in bounds[:-1]] + [0]
    hi = [(b[1] if b[1] is not None else np.inf) for b in bounds[:-1]] + [0]
    integer = milp(
        obj, integrality=np.ones(n + 2), bounds=Bounds(lo, hi),
        constraints=LinearConstraint(A, -np.inf, B),
        options={"time_limit": 8},
    )
    if not integer.success:
        return slack, None
    candidate = np.rint(integer.x).astype(int)
    assert np.all(A @ candidate <= B)
    return slack, candidate[:-2]


def verify(s, centers, lobes, multiplicities):
    base = template(s, centers, lobes)
    n = sum(multiplicities)
    full = [set() for _ in range(n)]
    vertex_types = [i for i, m in enumerate(multiplicities) for _ in range(m)]
    for x, i in enumerate(vertex_types):
        for y, j in enumerate(vertex_types[:x]):
            if i == j or j in base[i]:
                full[x].add(y)
                full[y].add(x)
    degree = sorted(map(len, full))
    k = degree[1]
    D = distances(full)
    e = ((D % 2 == 0) & (D > 0)).sum(axis=1)
    assert n > 3 * k + 2 and max(e) <= k and degree[0] >= 6
    for x in range(n):
        Dx = distances(full, x)
        assert max(Dx[y, z] for y in range(n) for z in range(n)
                   if y != x and z != x) < n
    assert len(lobes) > s + 1
    return n, k, [(u, v) for u in range(n) for v in sorted(full[u]) if u < v]


def search():
    previous = {}
    best = {}
    attempts = {}
    for it in range(30000):
        if not live():
            print("stop marker", flush=True)
            return
        s = (5, 6, 7, 8)[it % 4]
        density = RNG.uniform(0.28, 0.75)
        if s not in previous or (it // 4) % 30 == 0 or RNG.random() < 0.08:
            centers = random_center(s)
            lobes = [random_lobe(s, density) for _ in range(s + 2)]
            inherited = float("inf")
        else:
            centers, lobes, inherited = previous[s]
            lobes = list(lobes)
            name = RNG.randrange(len(lobes))
            if RNG.random() < 0.20:
                centers ^= 1 << RNG.randrange(s * (s - 1) // 2)
                edges = [len(v) for v in template(s, centers, [])]
                if max(edges) == s - 1 or max(edges) < 2:
                    continue
            elif RNG.random() < 0.40:
                lobes[name] = random_lobe(s, density)
            else:
                masks = list(lobes[name])
                j = RNG.randrange(len(masks))
                masks[j] ^= 1 << RNG.randrange(s)
                masks = sorted(set(masks))
                if len(masks) < 2 or np.bitwise_or.reduce(masks).bit_count() < 2:
                    continue
                lobes[name] = masks
        possible_low = None
        if RNG.random() < 0.25:
            possible_low = RNG.randrange(s + sum(map(len, lobes)))
        result = score(s, centers, lobes, possible_low)
        if result is None:
            continue
        attempts[s] = attempts.get(s, 0) + 1
        slack, multiplicities = result
        if slack < best.get(s, float("inf")) - 1e-8:
            best[s] = slack
            print("best", it, s, attempts[s], slack, centers, lobes, possible_low, flush=True)
        if multiplicities is not None:
            print("witness", verify(s, centers, lobes, multiplicities), flush=True)
            return
        if slack <= inherited or RNG.random() < 0.02:
            previous[s] = centers, lobes, slack
    print("finished", attempts, best, flush=True)


if __name__ == "__main__":
    search()
