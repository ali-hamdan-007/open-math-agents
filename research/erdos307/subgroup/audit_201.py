"""Exhaust the subgroup of all attainable product and reciprocal-sum pairs."""
from collections import deque
from math import gcd

modulus = 201
residue = 136
n = 1784
product = pow(residue, n, modulus)
reciprocal_sum = n * pow(residue, -1, modulus) % modulus
log_mod_three = {pow(4, j, 67): j % 3 for j in range(33)}
classes = [r for r in range(1, modulus) if gcd(r, modulus) == 1
           and r % 3 == log_mod_three[r*r % 67]]
assert len(classes) == 44 and residue in classes

def satisfies(state, m):
    a, u = state
    b = product * pow(a, -1, m) % m
    return (a*u-b) % m == 0 and (b*(reciprocal_sum-u)-a) % m == 0

def main():
    states = {(1, 0)}
    queue = deque(states)
    generators = [(r, pow(r, -1, modulus)) for r in classes]
    while queue:
        a, u = queue.popleft()
        for r, v in generators:
            other = (a*r % modulus, (u+v) % modulus)
            if other not in states:
                states.add(other)
                queue.append(other)
    print(f"reachable subgroup states: {len(states)}")
    for m in (3, 67, 201):
        matching = sum(satisfies(st, m) for st in states)
        print(f"modulus {m}: {matching} subgroup states satisfy both equations")
        assert (matching > 0) == (m != modulus)
    for k, m in ((7, 3), (1683, 67)):
        assert satisfies((pow(residue,k,m), k*pow(residue,-1,m)), m)
    a = pow(residue, 33, modulus)
    b = product * pow(a,-1,modulus) % modulus
    assert (a*a+b*b-product*reciprocal_sum) % modulus == 0

if __name__ == "__main__":
    main()
