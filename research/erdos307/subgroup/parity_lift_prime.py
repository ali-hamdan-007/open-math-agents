"""Integer upper bound for failures of parity-preserving local lifting."""

from argparse import ArgumentParser
from bisect import bisect_left
from math import isqrt

SCALE = 10**12
CERTIFIED_MODULI = {67: (700_000_000, 1_939_806_948_835)}


def prime_prefixes(modulus, limit):
    sieve = bytearray(b"\1") * (limit + 1)
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((limit - start) // prime + 1)
    assert 2 < modulus <= limit and sieve[modulus]

    weights = [[] for _ in range(modulus)]
    prefixes = [[0] for _ in range(modulus)]
    for prime in range(3, limit + 1, 2):
        if sieve[prime] and prime != modulus:
            residue = prime % modulus
            weight = (SCALE + prime - 1) // prime
            weights[residue].append(-weight)
            prefix = prefixes[residue]
            prefix.append(prefix[-1] + weight)
    return weights, prefixes


def penalized_prefixes(negative_weights, prefix, maximum, reserved, penalty):
    assert len(prefix) > maximum + reserved
    # Prefix increments decrease. Extending a prefix improves the objective
    # exactly while the next increment exceeds the penalty.
    cutoff = bisect_left(negative_weights, -penalty)
    result = []
    for count in range(maximum + 1):
        end = min(count + reserved, max(count, cutoff))
        result.append(prefix[end] - penalty * (end - count))
    return result


def opposite_pair_bound(left, right, block_length, choices, penalty):
    best = 0
    for count in range(choices + 1):
        for opposite_swaps in range(count + 1):
            homogeneous_blocks = count - opposite_swaps
            larger = opposite_swaps + block_length * (homogeneous_blocks + 1) - 1
            best = max(
                best,
                left[opposite_swaps] + right[larger] - penalty * count,
                right[opposite_swaps] + left[larger] - penalty * count,
            )
    return best


def upper_bound(modulus, weights, prefixes, placements, penalty):
    choices = modulus - 2
    reserved = modulus - 2 + placements
    upper = penalty * (choices + reserved)
    for residue in range(1, (modulus + 1) // 2):
        block_length = next(
            length for length in range(2, modulus, 2)
            if pow(residue, 2 * length, modulus) == 1
        )
        maximum = block_length * (choices + 1) - 1
        left, right = (
            penalized_prefixes(weights[r], prefixes[r], maximum, reserved, penalty)
            for r in (residue, modulus - residue)
        )
        upper += opposite_pair_bound(left, right, block_length, choices, penalty)
    return upper


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("modulus", type=int, nargs="?", default=67)
    parser.add_argument("--placements", type=int, default=6)
    parser.add_argument("--penalty", type=int)
    parser.add_argument("--sieve-limit", type=int, default=6_000_000)
    args = parser.parse_args()
    reference_penalty, reference_bound = CERTIFIED_MODULI.get(
        args.modulus, (700_000_000, None)
    )
    penalty = reference_penalty if args.penalty is None else args.penalty
    assert args.placements >= 0 and penalty >= 0
    weights, prefixes = prime_prefixes(args.modulus, args.sieve_limit)
    upper = upper_bound(args.modulus, weights, prefixes, args.placements, penalty)
    if reference_bound is not None and args.placements == 6 and penalty == reference_penalty:
        assert upper == reference_bound < 2 * SCALE
    print(f"modulus={args.modulus} placements={args.placements} scaled_mass_bound={upper}")


if __name__ == "__main__":
    main()
