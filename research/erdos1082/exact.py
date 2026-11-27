"""Exact squared-distance extension count for the five circular base forms.

t = 2*cos(pi/18), with minimal polynomial (t^3 - 3*t)^2 - 3 by Eisenstein.
Subtract the squared distance to the origin from each peripheral equation.
The first two equations determine the coordinates affinely in T = M^2.
The last two equations either determine T, constrain nothing, or contradict.
Only the original equation to the origin remains after this elimination.
"""

from collections import defaultdict
from itertools import combinations, product

from sympy import CRootOf, QQ, Symbol

x = Symbol("x")
K = QQ.algebraic_field(CRootOf((x**3 - 3*x)**2 - 3, 5))
t = K.unit
one = K.one
zero = K.zero
two = one + one
cosine_twice = [two, t]
for i in range(2, 36):
    cosine_twice.append(t * cosine_twice[i - 1] - cosine_twice[i - 2])

def coord(angle):
    return cosine_twice[angle % 36] / two, cosine_twice[(9-angle) % 36] / two

def dist_sq(base_a, base_b):
    return sum(((a-b)**2 for a,b in zip(base_a,base_b)), zero)

def exact(base, label):
    small = list(dict.fromkeys(dist_sq(a,b) for a,b in combinations(base,2)))
    assert len(small) == 3
    forms = [(d,zero) for d in small] + [(zero,one)]
    (p,q),(r,s),(u,v),(w,z) = base[1:]
    det = p*s-q*r
    assert det
    wildcard, forced = set(), defaultdict(set)
    for labels in product(range(4), repeat=5):
        # Coordinates are stored as (constant, coefficient of T).
        d = [forms[i] for i in labels]
        rhs = [((one+d[0][0]-a)/two,(d[0][1]-b)/two) for a,b in d[1:]]
        xx = tuple((s*a-q*b)/det for a,b in zip(rhs[0],rhs[1]))
        yy = tuple((p*b-r*a)/det for a,b in zip(rhs[0],rhs[1]))
        eqs = [tuple(a*b+c*e-f for b,e,f in zip(xx,yy,dval))
               for (a,c),dval in zip(((u,v),(w,z)),rhs[2:])]
        if any(a and not b for a,b in eqs):
            continue
        forced_values = {-a/b for a,b in eqs if b}
        if len(forced_values) > 1:
            continue
        if forced_values:
            T, = forced_values
            if T in small:
                continue
        else:
            assert 3 not in labels, (label, labels)
            T = zero
        a,b = (x0+x1*T for x0,x1 in (xx,yy))
        if (a,b) in base or a*a+b*b != d[0][0]+d[0][1]*T:
            continue
        if forced_values:
            forced[T].add((a,b))
        else:
            wildcard.add((a,b))
    bound = len(wildcard) + max(map(len,forced.values()), default=0)
    print(label, "wildcard", len(wildcard), "forced bucket sizes",
          sorted(map(len,forced.values())), "bound", bound)
    assert bound <= 4

def check():
    origin = (zero, zero)
    rt3 = cosine_twice[3]
    left = (rt3/two, -one/two)
    right = (rt3/two, one/two)
    for sign in (one, -one):
        exact([origin, left, right, (sign, zero), (sign/two, -sign*rt3/two)],
              f"123 sign {sign.to_list()}")
    for angle in (-1,-13,-25):
        yy = coord(angle)[1]
        assert (two*yy)**3 - (one+two)*(two*yy)-one == zero
        xx = (two+yy-(two+two)*yy**2)/rt3
        assert xx == coord(angle)[0]
        exact([origin, left, right, (xx, yy), (xx, -yy)], f"157 height slot {angle}")

if __name__ == "__main__":
    check()
