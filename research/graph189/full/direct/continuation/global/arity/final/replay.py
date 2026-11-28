"""Exact arithmetic replay for the Graph 189 separator and width reduction.

Run python3 replay.py and compare its tab-separated output with bands.tsv.
No external Python packages are required.
"""
import csv
import sys


def ceildiv(a, b):
    return -((-a) // b)


def width_possible(k, n):
    if n <= 4 * k + 2:
        return True
    def deficit(d):
        return (n-d-k-2) * (2*(n-2*k)+k*(d-k)) - (k+1)*k*d
    low = k + max(0, ceildiv(n-3*k-1, k))
    return low <= 3*k and min(deficit(low), deficit(3*k)) <= 0


def order_range(s, k):
    lo = (s+1)*(k-s+2)-1
    if k >= 4*s:
        lo = max(lo, min((s+2)*(k-2*s+2)-1, ceildiv(k*(k-1), 4)))
    hi = 2*k+1+s*k*k//(k-s)
    if k > 6*(s-1):
        hi = min(hi, ceildiv((2*s+3)*k, 2)+2*s+1,
                 ceildiv(((s+1)*(s-2)+3)*k, s-2)+2*s+2)
    if lo > hi or not width_possible(k, lo):
        return range(0)
    left, right = lo, hi
    while left < right:
        mid = (left+right+1)//2
        if width_possible(k, mid):
            left = mid
        else:
            right = mid-1
    return range(lo, left+1)


def smaller_side(s, k, h):
    mid = h//2
    def allowed(x):
        return x*(h-x-k) <= s*k*k
    if allowed(mid):
        return mid
    lo, hi = 0, mid
    while lo+1 < hi:
        x = (lo+hi)//2
        if allowed(x):
            lo = x
        else:
            hi = x
    return lo


def viable(s, k, n):
    limit = (k-1)//2
    low = 0
    while low <= limit and n > 3*k+1+low*(k-low-1):
        low += 1
    low = max(low, ceildiv(n-3*k-1, k-2))
    def usable(e):
        w = ceildiv(2*(n-2*k)+k*e, k+1)
        return w*(n-2*k-e-2) <= k*(k+e)
    # The deficit bound below becomes weaker as e increases.
    e = next((v for v in range(2*k, low-1, -1) if usable(v)), None)
    if e is None:
        return False
    a = smaller_side(s, k, n-s)
    debit = (s+1)*k-n+a+s
    deficit = max([0] + [
        min(r-1, (2*k+(k+1)*r-n)//k) for r in range(1, s+1)
        if (r-1)*(k-s+1) <= debit + r*(e+s-1)])
    lift_ready = (2*(k-deficit-1) > 3*s and
                  (k-2*deficit-2)//2+1 >= s+1 and 4*n < k*(k-1))
    return not lift_ready or n >= (s+2)*(k-deficit-s+1)-1


def verify_terminal(s, k, lo, hi):
    h = lo-s-1
    cap = smaller_side(s, k, h)
    a = cap+1
    b = h-k-a
    assert s >= 5 and k > 6*(s-1) and lo <= hi
    assert lo > (s+1)*k+2*s
    assert b >= k and a*b > s*k*k and b*(b-k) > s*k*k
    assert h > s*k+cap and cap < 2*k-s
    assert (s*k-s*(s-1)+cap+1)*s+cap < h*s
    for c in (1, 2):
        d = s-c
        assert (s*k+k-d*(d-1)+c+1)*d+k < h*d
    return cap


def rows():
    for s in range(5, 100):
        degrees = range(max(26, 3*s+1), 4*s*s+8*s-2)
        for k in degrees:
            possible = order_range(s, k)
            first = next((n for n in possible if viable(s,k,n)), None)
            if first is None:
                continue
            last = next(n for n in reversed(possible) if viable(s,k,n))
            yield s, k, first, last


if __name__ == '__main__':
    out = csv.writer(sys.stdout, delimiter='\t', lineterminator='\n')
    out.writerow(['s','k','nmin','nmax','Xcap'])
    for s,k,lo,hi in rows():
        cap = verify_terminal(s,k,lo,hi)
        out.writerow([s,k,lo,hi,cap])
