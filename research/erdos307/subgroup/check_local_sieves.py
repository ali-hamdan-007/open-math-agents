from fractions import Fraction
from itertools import combinations
from math import isqrt, prod


def state(support, selected, modulus):
    complement = tuple(i for i in range(len(support)) if i not in selected)
    p, q = ([support[i] for i in side] for side in (selected, complement))
    a, b = (prod(side) % modulus for side in (p, q))
    u, v = (sum(pow(x, -1, modulus) for x in side) % modulus for side in (p, q))
    return tuple(x % modulus for x in (a*a+b*b, u*v, a*u-b, b*v-a))


def square_2adic(n):
    if n == 0:
        return True
    v = (abs(n) & -abs(n)).bit_length() - 1
    return v % 2 == 0 and (n >> v) % 8 == 1


first_forty = [p for p in range(2, 200)
                if all(p % d for d in range(2, isqrt(p)+1))][:40]
assert len(first_forty) == 40
assert sum((Fraction(1, p) for p in first_forty), Fraction(0)) < 2

seven = (1,)*5 + (2,)
seven_states = {state(seven, set(indices), 7)
                for count in range(1, len(seven))
                for indices in combinations(range(len(seven)), count)}
assert {row[0] for row in seven_states} == {5}
assert any(row[1] == 1 for row in seven_states)
assert any(row[2] == 0 for row in seven_states)
assert any(row[3] == 0 for row in seven_states)
assert 4*4 % 7 == 2 and (4*4+4*4) % 7 == 4
print("mod 7: subgroup and separate tests pass; actual products reject")

five = (1, 1, 1, 2, 3, 4)
five_rows = []
expected = [(2, 2, 4, 0), (3, 0, 3, 2), (3, 2, 4, 1), (2, 1, 3, 2),
            (2, 1, 2, 3), (3, 2, 1, 4), (3, 0, 2, 3), (2, 2, 0, 4)]
for count in range(4):
    for exceptional in combinations(range(3, 6), count):
        selected = set(range(3-count)) | set(exceptional)
        five_rows.append(state(five, selected, 5))
assert five_rows == expected
assert all(row[2:] != (0, 0) for row in five_rows)
assert all(any(row[column] == target for row in five_rows)
           for column, target in enumerate((3, 1, 0, 0)))
print("mod 5: both projections and both separate swaps pass; every joint row fails")

support = (41, 61, 181, 157, 113, 449)
assert tuple(p % 5 for p in support) == five
assert all(all(p % d for d in range(2, isqrt(p)+1)) for p in support)
n = prod(support)
c = sum(n//p for p in support)
assert all(pow(n//p, (p-1)//2, p) == 1 for p in support)
assert square_2adic(c-2*n) and square_2adic(c+2*n)
assert sum((Fraction(1, p) for p in support), Fraction(0)) < 2
for count in (1, 3, 5):
    for selected in combinations(range(len(support)), count):
        assert state(support, set(selected), 5)[2:] != (0, 0)
print("six-prime test: internal, 2-adic, and all odd partitions checked")
