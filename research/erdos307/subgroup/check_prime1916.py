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
