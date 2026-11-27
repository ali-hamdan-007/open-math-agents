"""Necessary endpoint-rotation conditions for a path missing its only low vertex."""
from collections import Counter
from functools import cache
from itertools import accumulate
from sys import argv


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, slots - 1):
            yield (first,) + rest


def normalize(positions, order):
    reverse = tuple(order + 1 - t for t in reversed(positions))
    return min(positions, reverse)


def rotation_core(k, n, d, omitted):
    order = n - 1
    room = order - d - 2 - (d - 1) * omitted
    if room < 0:
        return 0, 0, 0
    base = [1] + [omitted] * (d - 1) + [1]
    states = set()
    for extra in compositions(room, d + 1):
        gaps = [x + y for x, y in zip(base, extra)]
        pos = tuple(x + i + 1 for i, x in enumerate(accumulate(gaps[:-1])))
        states.add(normalize(pos, order))
    turns = {}
    for state in states:
        ends = []
        for anchors in (state, tuple(order+1-j for j in reversed(state))):
            out = Counter()
            for pivot in range(2, order):
                dest = tuple(sorted(pivot-j if j<pivot else j for j in anchors))
                key = normalize(dest, order)
                if key in states:
                    out[key] += 1
            ends.append(out)
        turns[state] = ends
    viable = states.copy()
    rounds = 0
    while viable:
        keep = {a for a in viable if all(sum(v for b, v in end.items() if b in viable) >= k
                                        for end in turns[a])}
        if keep == viable:
            break
        viable = keep
        rounds += 1
    return len(states), len(viable), rounds


def scan():
    d = 4
    for k in range(8, 19):
        for n in range(1, 3*k+3):
            remaining = []
            for m in range(k//2+1, (n-4)//3):
                if m*(k-m) > n-4:
                    continue
                initial, survived, rounds = rotation_core(k,n,d,m)
                if survived:
                    remaining.append((m,initial,survived,rounds))
            if remaining:
                print(k,n,remaining, flush=True)


if __name__=='__main__':
    scan() if len(argv)==1 else print(rotation_core(*map(int,argv[1:])))
