"""Enumerate the remaining (connectivity, second degree, minimum order, maximum order) rows.

Run with Python 3.8 or newer, using only the standard library.
"""
import argparse
from math import isqrt
from pathlib import Path
from time import monotonic


def ceil_div(numerator, denominator):
    return -(-numerator // denominator)


def minimum_excess(n, k):
    # The matched rooted-Ore obstruction applies through floor((k-1)/2).
    low, high = 0, (k - 1) // 2 + 1
    while low < high:
        mid = (low + high) // 2
        if 3 * k + 1 + mid * (k - mid - 1) < n:
            low = mid + 1
        else:
            high = mid
    return max(low, ceil_div(n - 3 * k - 1, k - 2))


def relaxed_difference(n, k, excess):
    m = n - 2 * k
    return ((m - excess - 2) * (2 * m + k * excess)
            - (k + 1) * k * (k + excess))


def minimum_width(n, k, excess):
    width = ceil_div(2 * (n - 2 * k) + k * excess, k + 1)
    while width - 2 - excess <= k - 3:
        capacity = width - 2 - excess
        if capacity >= 0:
            left = capacity // 2
            right = capacity - left
            packed = left * (k - left - 1) + right * (k - right - 1)
            if 2 * n <= 6 * k + width + packed:
                break
        width += 1
    return width


def maximum_small_side(n, k, s):
    high_total = n - s
    midpoint = high_total // 2

    def allowed(size):
        return size * (high_total - size - k) <= s * k * k

    if allowed(midpoint):
        return midpoint
    low, high = 0, midpoint
    while low + 1 < high:
        mid = (low + high) // 2
        if allowed(mid):
            low = mid
        else:
            high = mid
    return low


def cut_deficit(n, k, s, excess, side_max):
    debit_max = (s + 1) * k - n + side_max + s
    deficit = 0
    for shared in range(1, s + 1):
        if (shared - 1) * (k - s + 1) <= debit_max + shared * (excess + s - 1):
            upper = min(shared - 1, (2 * k + (k + 1) * shared - n) // k)
            deficit = max(deficit, upper)
    return deficit


def lift_threshold(k, s, deficit):
    # These sufficient conditions allow the critical-vertex lift in every
    # possible deficit case. A genuine low on no minimum cut already lifts.
    critical = k - deficit - 1 > (3 * s) // 2
    exterior_cycle = (k - 2 * deficit - 2) // 2 + 1 >= s + 1
    if critical and exterior_cycle:
        return min((s + 2) * (k - deficit - s + 1) - 1, ceil_div(k * (k - 1), 4))
    return 0


def low_cut_allows(n, k, s, excess):
    deficit = cut_deficit(n, k, s, excess, maximum_small_side(n, k, s))
    return n >= lift_threshold(k, s, deficit)


def uniform_lift(lower, k, s):
    # Bound all subsequent orders by X(X-k)<=sk^2 and the relaxed width at lower.
    side_max = (k + isqrt((1 + 4 * s) * k * k)) // 2
    left, right = minimum_excess(lower, k), 2 * k
    if relaxed_difference(lower, k, right) > 0:
        while left < right:
            mid = (left + right + 1) // 2
            if relaxed_difference(lower, k, mid) <= 0:
                left = mid
            else:
                right = mid - 1
        max_excess = left
    else:
        max_excess = right
    deficit = cut_deficit(lower, k, s, max_excess, side_max)
    return lift_threshold(k, s, deficit)


def allows(n, k, s=None, relax=False):
    smallest = minimum_excess(n, k)
    largest = 2 * k
    if smallest > largest:
        return False
    far_value = relaxed_difference(n, k, largest)
    if min(relaxed_difference(n, k, smallest), far_value) > 0:
        return False
    if relax:
        return True
    for excess in range(smallest, largest + 1):
        if far_value > 0 and relaxed_difference(n, k, excess) > 0:
            # The relaxed difference is concave in excess on this interval.
            return False
        width = minimum_width(n, k, excess)
        if width * (n - 2 * k - excess - 2) <= k * (k + excess):
            if s is None or low_cut_allows(n, k, s, excess):
                return True
    return False


def order_bounds(k, s):
    lower = (s + 1) * (k - s + 2) - 1
    if not allows(lower, k, relax=True):
        return None
    upper = min(2 * k + 1 + isqrt(k * k * (k + 1) + 1),
                2 * k + 1 + s * k * k // (k - s))
    if k > 6 * (s - 1):
        upper = min(upper, ceil_div((2 * s + 3) * k, 2) + 2 * s + 1,
                    ((s + 1) * (s - 2) + 3) * k // (s - 2) + s + 2)
    lower = max(lower, uniform_lift(lower, k, s))
    if lower > upper or not allows(lower, k):
        return None
    # The width-only constraints allow an initial interval in n.
    left, right = lower, upper
    while left < right:
        mid = (left + right + 1) // 2
        if allows(mid, k):
            left = mid
        else:
            right = mid - 1
    upper = left
    first = next((n for n in range(lower, upper + 1) if allows(n, k, s)), None)
    if first is None:
        return None
    last = next(n for n in range(upper, first - 1, -1) if allows(n, k, s))
    return first, last


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lease-dir', type=Path, help='optional research-run sentinel directory')
    args = parser.parse_args()
    next_lease_check = 0.0
    for s in range(5, 64):
        for k in range(max(25, 5 * s) + 1, 4 * s * s + 8 * s - 2):
            if args.lease_dir is not None and monotonic() >= next_lease_check:
                next_lease_check = monotonic() + 0.1
                if not (args.lease_dir / 'LIVE').exists() or any(
                        (args.lease_dir / flag).exists() for flag in ('PAUSE', 'HALT')):
                    raise SystemExit('Research run paused')
            bounds = order_bounds(k, s)
            if bounds is not None:
                print(s, k, *bounds)


if __name__ == '__main__':
    main()
