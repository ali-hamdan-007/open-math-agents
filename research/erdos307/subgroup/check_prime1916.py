from math import isqrt, lcm

scale = 10**9
for ell in (3, 5, 7, 11, 13, 17, 19, 23, 29):
    steps = [lcm(2, next(j for j in range(1, ell)
                         if pow(r, 2*j, ell) == 1)) for r in range(1, ell)]
    cutoff = 1 + max(steps)*(ell-2) + 2*sum(d-1 for d in steps) + 6
    count, mass_upper = 0, 0
    for p in range(3, 100000, 2):
        if p == ell or any(p % d == 0 for d in range(3, isqrt(p)+1, 2)):
            continue
        count += 1
        mass_upper += (scale + p - 1)//p
        if count == cutoff-1:
            break
    assert count == cutoff-1 and mass_upper < 2*scale
    print(ell, cutoff, mass_upper)

from collections import defaultdict

for ell in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
    steps = {r: lcm(2, next(j for j in range(1, ell)
                            if pow(r, 2*j, ell) == 1))
             for r in range(1, ell)}
    targets = {r: 2*(d-1) + d*(ell-2) + 6 for r, d in steps.items()}
    terms = defaultdict(list)
    remaining = sum(targets.values())
    for p in range(3, 1000000, 2):
        r = p % ell
        if not r or len(terms[r]) == targets[r]:
            continue
        if any(p % d == 0 for d in range(3, isqrt(p)+1, 2)):
            continue
        terms[r].append((scale+p-1)//p)
        remaining -= 1
        if remaining == 0:
            break
    assert remaining == 0
    baseline = 0
    blocks, reservations = [], []
    for r, d in steps.items():
        base = 2*(d-1)
        baseline += sum(terms[r][:base])
        for j in range(ell-2):
            blocks.append(sum(terms[r][base+j*d:base+(j+1)*d]))
        reservations.extend(terms[r][base:base+6])
    bound = (baseline + sum(sorted(blocks, reverse=True)[:ell-2])
             + sum(sorted(reservations, reverse=True)[:6]))
    assert bound < 2*scale
    print(ell, bound)
