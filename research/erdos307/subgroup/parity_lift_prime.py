"""Integer upper bounds on reciprocal mass when prescribed-product lifting fails."""

from argparse import ArgumentParser
from array import array
from bisect import bisect_left
from functools import cache
from heapq import nsmallest
from itertools import chain
from math import isqrt

SCALE = 10**12
DEFAULT_PENALTY = 500_000_000
CERTIFIED_BOUNDS = {
    3: 891_949_076_520,
    5: 1_259_942_070_368,
    7: 1_438_895_441_121,
    11: 1_609_200_422_313,
    13: 1_629_636_832_663,
    17: 1_679_616_754_632,
    19: 1_720_380_438_123,
    23: 1_763_226_387_916,
    29: 1_776_347_080_672,
    31: 1_789_563_151_012,
    37: 1_795_018_919_297,
    41: 1_800_548_364_077,
    43: 1_823_730_230_558,
    47: 1_844_854_809_441,
    53: 1_838_199_427_067,
    59: 1_868_715_043_441,
    61: 1_841_507_191_181,
    67: 1_872_115_564_086,
    71: 1_878_800_918_624,
    73: 1_858_591_943_625,
    79: 1_894_430_741_086,
    83: 1_910_700_346_814,
    89: 1_893_431_160_928,
    97: 1_895_773_804_500,
    101: 1_917_865_786_653,
    103: 1_932_289_872_165,
    107: 1_952_126_888_080,
    109: 1_926_699_718_934,
    113: 1_923_665_808_774,
    127: 1_962_956_801_455,
    131: 1_971_677_167_225,
    137: 1_967_148_934_214,
    139: 1_986_266_937_793,
    149: 1_989_238_996_898,
    151: 1_992_926_193_872,
    157: 1_988_539_824_517,
}
REFINED_BOUNDS = {
    163: (1_976_862_210_857, 1_868_218_744_822),
    167: (1_993_475_015_074, 1_748_596_380_450),
    173: (1_961_573_337_158, 1_785_518_501_559),
    181: (1_953_141_416_671, 1_941_771_889_744),
}
SAFE_PRIME_BOUNDS = {179: (1_973_320_224_830, 1_576_711_291_747)}
CERTIFIED_PENALTIES = dict.fromkeys((149, 151, 157, *REFINED_BOUNDS, *SAFE_PRIME_BOUNDS), 450_000_000)


def prime_prefixes(modulus, limit, maximum_prefixes):
    sieve = bytearray(b"\1") * (limit + 1)
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((limit - start) // prime + 1)
    assert 2 < modulus <= limit and sieve[modulus]

    negative_weights = [array("q") for _ in range(modulus)]
    prefixes = [array("q", (0,)) for _ in range(modulus)]
    remaining = modulus - 1
    for prime in range(3, limit + 1, 2):
        if sieve[prime] and prime != modulus:
            residue = prime % modulus
            if len(negative_weights[residue]) < maximum_prefixes[residue]:
                weight = (SCALE + prime - 1) // prime
                negative_weights[residue].append(-weight)
                prefix = prefixes[residue]
                prefix.append(prefix[-1] + weight)
                if len(negative_weights[residue]) == maximum_prefixes[residue]:
                    remaining -= 1
                    if remaining == 0:
                        break
    return negative_weights, prefixes


def penalized_prefixes(negative_weights, prefix, maximum, reserved, penalty):
    assert len(prefix) > maximum + reserved
    # Extending the prefix improves the score while its next weight exceeds L.
    cutoff = bisect_left(negative_weights, -penalty)
    result = []
    for count in range(maximum + 1):
        end = min(count + reserved, max(count, cutoff))
        result.append(prefix[end] - penalty * (end - count))
    return result


def opposite_pair_bound(left, right, block_length, choices, penalty):
    best = 0
    for count in range(choices + 1):
        for swaps in range(count + 1):
            blocks = count - swaps
            larger = swaps + block_length * (blocks + 1) - 1
            best = max(
                best,
                left[swaps] + right[larger] - penalty * count,
                right[swaps] + left[larger] - penalty * count,
            )
    return best


def orientation_bound(light, heavy, excess, cap, penalty):
    # The penalized prefixes are discretely concave, so the sum's next
    # increment decreases with the number of opposite swaps.
    lo, hi = 0, cap
    while lo < hi:
        mid = (lo + hi) // 2
        light_increment = light[mid + 1] - light[mid]
        heavy_increment = heavy[excess + mid + 1] - heavy[excess + mid]
        if light_increment + heavy_increment > penalty:
            lo = mid + 1
        else:
            hi = mid
    return light[lo] + heavy[excess + lo] - penalty * lo


def pair_score(prefixes, penalty):
    @cache
    def score(excess, cap):
        left, right = prefixes
        return max(
            orientation_bound(left, right, excess, cap, penalty),
            orientation_bound(right, left, excess, cap, penalty),
        )

    return score


def inverse_pair_bound(pair1, pair2, block_length, choices, penalty):
    best = 0
    for big, small in ((pair1, pair2), (pair2, pair1)):
        big_score = pair_score(big, penalty)
        small_score = pair_score(small, penalty)
        for inverse_swaps in range(choices + 1):
            for blocks in range(choices - inverse_swaps + 1):
                used = inverse_swaps + blocks
                cap = choices - used
                excess = inverse_swaps + block_length * (blocks + 1) - 1
                best = max(
                    best,
                    big_score(excess, cap) + small_score(inverse_swaps, cap) - penalty * used,
                )
    return best


def inverse_directions(modulus):
    seen = set()
    for residue in range(1, (modulus + 1) // 2):
        if residue in seen:
            continue
        inverse = pow(residue, -1, modulus)
        inverse = min(inverse, modulus - inverse)
        seen.update((residue, inverse))
        block_length = next(
            length for length in range(2, modulus, 2)
            if pow(residue, 2 * length, modulus) == 1
        )
        yield residue, inverse, block_length


def direction_members(modulus, residue, inverse):
    return tuple(sorted({residue, modulus - residue, inverse, modulus - inverse}))


def mass_bound_for_direction(modulus, direction, weights, prefixes, choices, reserved, penalty):
    residue, inverse, block_length = direction
    maximum = block_length * (choices + 1) - 1

    def adjusted(r):
        return tuple(
            penalized_prefixes(weights[s], prefixes[s], maximum, reserved, penalty)
            for s in (r, modulus - r)
        )

    first = adjusted(residue)
    if residue == inverse:
        return opposite_pair_bound(*first, block_length, choices, penalty)
    return inverse_pair_bound(first, adjusted(inverse), block_length, choices, penalty)


def safe_prime_bounds(modulus, placements, penalty, directions, weights, prefixes):
    square_order = (modulus - 1) // 2
    assert all(square_order % divisor != 0 for divisor in range(2, isqrt(square_order) + 1))
    distinct = next(
        count for count in range(3, square_order + 1)
        if all(k * (count - k) >= square_order - 1 for k in (count // 2, count // 2 - 1))
    )
    choices = modulus - 2
    reserved = choices + placements
    dense = penalty * (choices + distinct + placements)
    sparse = penalty * (choices + reserved)
    table = [[0] * (placements + 1) for _ in range(distinct)]
    for direction in directions:
        r, t, block_length = direction
        dense += mass_bound_for_direction(
            modulus, direction, weights, prefixes, choices, distinct + placements, penalty
        )
        both = mass_bound_for_direction(modulus, direction, weights, prefixes, choices, reserved, penalty)
        if block_length != modulus - 1:
            sparse += both
            continue
        assert r != t
        active_left, active_right = (
            mass_bound_for_direction(modulus, (a, a, block_length), weights, prefixes, choices, reserved, penalty)
            for a in (r, t)
        )

        def fixed_only(a, count):
            return max(
                prefixes[a][i] + prefixes[modulus - a][count - i]
                for i in range(count + 1)
            ) - penalty * count

        fixed_left, fixed_right = (
            [fixed_only(a, count) for count in range(placements + 1)]
            for a in (r, t)
        )
        neither = [
            max(fixed_left[i] + fixed_right[count - i] for i in range(count + 1))
            for count in range(placements + 1)
        ]
        one = [
            max(active_left + fixed_right[count], active_right + fixed_left[count])
            for count in range(placements + 1)
        ]
        table = [
            [
                max(
                    max(table[classes][fixed - i] + neither[i] for i in range(fixed + 1)),
                    max(table[classes - 1][fixed - i] + one[i] for i in range(fixed + 1)) if classes >= 1 else 0,
                    table[classes - 2][fixed] + both if classes >= 2 else 0,
                )
                for fixed in range(placements + 1)
            ]
            for classes in range(distinct)
        ]
    return dense, sparse + table[-1][-1]


def reciprocal_mass_bounds(modulus, placements, penalty, sieve_limit, method):
    choices = modulus - 2
    reserved = modulus - 2 + placements
    directions = list(inverse_directions(modulus))
    greatest_order = max(d for _, _, d in directions)
    if sieve_limit is None:
        sieve_limit = max(100_000, 22 * modulus**2 * greatest_order)
    maximum_prefixes = [0] * modulus
    for residue, inverse, block_length in directions:
        maximum = block_length * (choices + 1) - 1 + reserved
        for member in direction_members(modulus, residue, inverse):
            maximum_prefixes[member] = maximum
    weights, prefixes = prime_prefixes(modulus, sieve_limit, maximum_prefixes)

    if method == "safe":
        return safe_prime_bounds(modulus, placements, penalty, directions, weights, prefixes)

    upper = penalty * (choices + reserved)
    if method == "basic":
        for direction in directions:
            upper += mass_bound_for_direction(
                modulus, direction, weights, prefixes, choices, reserved, penalty
            )
        return (upper,)

    half = greatest_order // 2
    quotient_reservations = (modulus - 1) // greatest_order - 1
    dense_reserve = half + quotient_reservations + placements
    dense = penalty * (choices + dense_reserve)
    sparse = upper
    subgroups = {}
    for direction in directions:
        residue, inverse, block_length = direction
        dense += mass_bound_for_direction(
            modulus, direction, weights, prefixes, choices, dense_reserve, penalty
        )
        standard = mass_bound_for_direction(
            modulus, direction, weights, prefixes, choices, reserved, penalty
        )
        if block_length != greatest_order:
            sparse += standard
            continue
        subgroup = frozenset(
            (pow(residue, 2 * exponent, modulus), exponent % 2)
            for exponent in range(greatest_order)
        )
        members = direction_members(modulus, residue, inverse)
        subgroups.setdefault(subgroup, []).append((members, standard))

    outside = half - 1 + placements
    for subgroup_directions in subgroups.values():
        worst = 0
        for members, standard in subgroup_directions:
            outside_weights = chain.from_iterable(
                weights[r][:outside]
                for other_members, _ in subgroup_directions
                if other_members != members
                for r in other_members
            )
            worst = max(worst, standard - sum(nsmallest(outside, outside_weights)))
        sparse += worst
    return dense, sparse

def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("moduli", type=int, nargs="*", default=[67])
    parser.add_argument("--placements", type=int, default=6)
    parser.add_argument("--penalty", type=int)
    parser.add_argument("--sieve-limit", type=int)
    parser.add_argument("--all", action="store_true", help="replay all certified moduli")
    parser.add_argument("--refined", action="store_true", help="use the cyclic subgroup cases")
    args = parser.parse_args()
    assert args.placements >= 0 and (args.penalty is None or args.penalty >= 0)
    certified_moduli = sorted(CERTIFIED_BOUNDS.keys() | REFINED_BOUNDS.keys() | SAFE_PRIME_BOUNDS.keys())
    for modulus in certified_moduli if args.all else args.moduli:
        assert modulus >= 3 and modulus % 2 == 1
        reference_penalty = CERTIFIED_PENALTIES.get(modulus, DEFAULT_PENALTY)
        penalty = reference_penalty if args.penalty is None else args.penalty
        if args.refined or modulus in REFINED_BOUNDS:
            method = "refined"
            expected = REFINED_BOUNDS.get(modulus)
        elif modulus in SAFE_PRIME_BOUNDS:
            method = "safe"
            expected = SAFE_PRIME_BOUNDS[modulus]
        else:
            method = "basic"
            expected = (CERTIFIED_BOUNDS[modulus],) if modulus in CERTIFIED_BOUNDS else None
        bounds = reciprocal_mass_bounds(modulus, args.placements, penalty, args.sieve_limit, method)
        if args.placements == 6 and penalty == reference_penalty and expected is not None:
            assert bounds == expected and max(bounds) < 2 * SCALE
        print(f"modulus={modulus} placements={args.placements} scaled_mass_bound={max(bounds)}")
        if len(bounds) == 2:
            print(f"  dense_bound={bounds[0]} sparse_bound={bounds[1]}")



if __name__ == "__main__":
    main()
