"""Integer certificates for simultaneous squared-product lifts at odd composite moduli."""

from argparse import ArgumentParser
from array import array
from bisect import bisect_left
from math import gcd, isqrt

SCALE = 10**12
PENALTY = 300_000_000
CERTIFIED_BOUNDS = {
    159: 1_639_680_115_190,
    161: 1_841_035_381_514,
    177: 1_691_348_517_185,
    185: 1_753_851_992_730,
    295: 1_902_528_134_373,
}


def quadratic_parity_group(modulus):
    units = [r for r in range(1, modulus) if gcd(r, modulus) == 1]
    order = 2 * len({r * r % modulus for r in units})
    assert gcd(modulus, order) == 1
    block_lengths = {}
    for residue in units:
        if residue >= modulus - residue:
            break
        block_lengths[residue] = next(
            length for length in range(2, order + 1, 2)
            if pow(residue, 2 * length, modulus) == 1
        )
    return order, block_lengths


def prime_prefixes(modulus, block_lengths, choice_budget, reserved_budget, sieve_limit):
    maximum = [0] * modulus
    for residue, block_length in block_lengths.items():
        cap = block_length * (choice_budget + 1) - 1 + reserved_budget
        maximum[residue] = cap
        maximum[modulus - residue] = cap

    sieve = bytearray(b"\1") * (sieve_limit + 1)
    for prime in range(2, isqrt(sieve_limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((sieve_limit - start) // prime + 1)

    weights = [array("q") for _ in range(modulus)]
    prefixes = [array("q", (0,)) for _ in range(modulus)]
    remaining = 2 * len(block_lengths)
    for prime in range(3, sieve_limit + 1, 2):
        if not sieve[prime]:
            continue
        residue = prime % modulus
        if len(weights[residue]) >= maximum[residue]:
            continue
        weight = (SCALE + prime - 1) // prime
        weights[residue].append(-weight)
        prefixes[residue].append(prefixes[residue][-1] + weight)
        if len(weights[residue]) == maximum[residue]:
            remaining -= 1
            if remaining == 0:
                break
    assert remaining == 0, "increase the sieve limit to fill all required prime prefixes"
    return weights, prefixes


def penalized_prefixes(weights, prefix, max_unreserved, reserved_budget):
    cutoff = bisect_left(weights, -PENALTY)
    values = []
    for count in range(max_unreserved + 1):
        end = min(count + reserved_budget, max(count, cutoff))
        values.append(prefix[end] - PENALTY * (end - count))
    return values


def opposite_pair_bound(left, right, block_length, choice_budget):
    bound = 0
    for choices in range(choice_budget + 1):
        for swaps in range(choices + 1):
            blocks = choices - swaps
            large = swaps + block_length * (blocks + 1) - 1
            bound = max(
                bound,
                left[swaps] + right[large] - PENALTY * choices,
                left[large] + right[swaps] - PENALTY * choices,
            )
    return bound


def mass_bound(modulus, placements, sieve_limit):
    group_order, block_lengths = quadratic_parity_group(modulus)
    choice_budget = modulus - 2
    reserved_budget = group_order - 1 + placements
    if sieve_limit is None:
        sieve_limit = 44 * len(block_lengths) * max(block_lengths.values()) * (choice_budget + 1)
    weights, prefixes = prime_prefixes(
        modulus, block_lengths, choice_budget, reserved_budget, sieve_limit
    )
    bound = PENALTY * (choice_budget + reserved_budget)
    for residue, block_length in block_lengths.items():
        maximum = block_length * (choice_budget + 1) - 1
        left, right = (
            penalized_prefixes(weights[r], prefixes[r], maximum, reserved_budget)
            for r in (residue, modulus - residue)
        )
        bound += opposite_pair_bound(left, right, block_length, choice_budget)
    return bound


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("moduli", type=int, nargs="*", default=[295])
    parser.add_argument("--placements", type=int, default=6)
    parser.add_argument("--sieve-limit", type=int)
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    assert args.placements >= 0
    for modulus in sorted(CERTIFIED_BOUNDS) if args.all else args.moduli:
        assert modulus >= 3 and modulus % 2 == 1
        upper = mass_bound(modulus, args.placements, args.sieve_limit)
        if args.placements == 6 and modulus in CERTIFIED_BOUNDS:
            assert upper == CERTIFIED_BOUNDS[modulus] < 2 * SCALE
        print(f"modulus={modulus} placements={args.placements} scaled_mass_bound={upper}")


if __name__ == "__main__":
    main()
