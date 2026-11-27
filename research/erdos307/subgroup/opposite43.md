# Opposite residue classes repair a mod-43 witness

Take ℓ=43 and put d_r=lcm(2, ord(r²)). Put q_1=q_36=q_37=1 and
q_42=2, with all other q_r=0. For each nonzero residue r, take the
first m_r=2d_r−2+d_r q_r−[r=3]−[r=20] odd primes in that residue.
The resulting support S has 2340 primes and reciprocal mass at least
2.001151508208. Take as witness T the first a_r=d_r−1−[r=3] primes
within each class. Its two sides have sizes 1161 and 1179.

Working modulo 43, this support has N=38 and C=34, and the witness has
x=A²=24, so x+N²/x=C. The reciprocal sum starts at U=14. Keeping every
selected class count congruent to its witness count modulo d_r allows
one shift each by 2, −7, and −1, and two shifts by −2, independently.
The resulting sums are exactly {2,3,…,16}. Thus this class-count
preserving construction cannot reach the target N/x=41. Reserving any
primes on either side only restricts this same family. This shows a
limitation of the proof starting from an arbitrary quadratic witness.
In this example exchanging 4241 for 3671 reaches the target and even preserves both exact side sizes.

More generally, fix the total number t of selected primes in each pair of opposite classes r and −r, with populations m and n. The number chosen from class r runs over every integer from max(0,t−n) to min(m,t). Thus the reciprocal sum admits w=min(m,n,t,m+n−t) successive increments of 2/r. Each replacement preserves the size and squared product. The pairs are disjoint. If the widths sum to at least ℓ−1 then every reciprocal residue occurs at this same exact size and squared product: each nonzero increment enlarges a proper subset of the prime field by at least one when its translate is adjoined. For the displayed example the sum of the widths is checked below.

The following Python verifies the example with integer arithmetic.
The floor sum certifies a lower bound for the exact reciprocal mass.

```python
from math import isqrt, lcm, prod

ell = 43
limit = 34501
prime = bytearray(b"\1") * (limit + 1)
for p in range(2, isqrt(limit) + 1):
    if prime[p]:
        prime[p*p::p] = bytes((limit - p*p)//p + 1)

classes = [[] for _ in range(ell)]
for p in range(3, limit + 1, 2):
    if prime[p] and p != ell:
        classes[p % ell].append(p)

blocks = {1: 1, 36: 1, 37: 1, 42: 2}
support, witness, shifts = [], [], []
for r in range(1, ell):
    order = next(k for k in range(1, ell) if pow(r, 2*k, ell) == 1)
    d = lcm(2, order)
    m = 2*d - 2 + d*blocks.get(r, 0) - (r == 3) - (r == 20)
    a = d - 1 - (r == 3)
    assert 0 <= a <= m <= len(classes[r])
    support.extend(classes[r][:m])
    witness.extend(classes[r][:a])
    shifts.extend([d * pow(r, -1, ell) % ell] * ((m - a)//d))

assert (len(support), len(witness)) == (2340, 1161)
assert sum(10**12 // p for p in support) == 2001151508208
N = prod(support) % ell
C = N * sum(pow(p, -1, ell) for p in support) % ell
x = pow(prod(witness), 2, ell)
assert (N, C, x) == (38, 34, 24)
assert (x + N*N*pow(x, -1, ell)) % ell == C
target = N * pow(x, -1, ell) % ell
sums = {sum(pow(p, -1, ell) for p in witness) % ell}
for shift in shifts:
    sums |= {(u + shift) % ell for u in sums}
assert sums == set(range(2, 17))
assert target == 41 and target not in sums

from collections import Counter
m = Counter(p % ell for p in support)
t = Counter(p % ell for p in witness)
width = sum(min(m[r], m[-r % ell], t[r]+t[-r % ell],
                m[r]+m[-r % ell]-t[r]-t[-r % ell]) for r in range(1,22))
assert 4241 in witness and 3671 in support and 3671 not in witness
swapped = (set(witness) - {4241}) | {3671}
A = prod(swapped) % ell
B = N * pow(A,-1,ell) % ell
U = sum(pow(p,-1,ell) for p in swapped) % ell
V = sum(pow(p,-1,ell) for p in set(support)-swapped) % ell
assert (A,B,U,V) == (29,28,41,21)
assert A*U % ell == B and B*V % ell == A
assert width == 1160
```
