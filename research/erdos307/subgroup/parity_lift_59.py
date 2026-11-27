"""Integer mass certificate for the mod-59 parity-preserving lift."""

from math import isqrt


MODULUS = 59
SCALE = 10**12
PENALTY = SCALE // 1000
BLOCK_BUDGET = 57
RESERVATION_BUDGET = 63
MAX_CLASS_INDEX = 58 * (BLOCK_BUDGET + 1) - 1
SIEVE_LIMIT = 3_500_000


def eligible_primes():
    sieve = bytearray(b"\1") * (SIEVE_LIMIT + 1)
    for prime in range(2, isqrt(SIEVE_LIMIT) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((SIEVE_LIMIT - start) // prime + 1)
    return [
        prime
        for prime in range(3, SIEVE_LIMIT + 1, 2)
        if sieve[prime] and prime != MODULUS
    ]


def reciprocal_upper(prime):
    return (SCALE + prime - 1) // prime


def penalized_prefixes(primes):
    prefixes = [[0] for _ in range(MODULUS)]
    for prime in primes:
        prefix = prefixes[prime % MODULUS]
        prefix.append(prefix[-1] + reciprocal_upper(prime))
    assert all(
        len(prefix) > MAX_CLASS_INDEX + RESERVATION_BUDGET
        for prefix in prefixes[1:]
    )
    return [
        [
            max(
                prefix[count + extra] - PENALTY * extra
                for extra in range(RESERVATION_BUDGET + 1)
            )
            for count in range(MAX_CLASS_INDEX + 1)
        ]
        for prefix in prefixes[1:]
    ]


def pair_bound(left, right, block_length):
    best = 0
    for blocks in range(BLOCK_BUDGET + 1):
        for opposite_swaps in range(blocks + 1):
            excess_blocks = blocks - opposite_swaps
            large_class = opposite_swaps + block_length * (excess_blocks + 1) - 1
            best = max(
                best,
                left[opposite_swaps] + right[large_class] - PENALTY * blocks,
                left[large_class] + right[opposite_swaps] - PENALTY * blocks,
            )
    return best


def main():
    primes = eligible_primes()
    small_support_upper = sum(map(reciprocal_upper, primes[:294]))
    assert small_support_upper < 2 * SCALE

    adjusted = penalized_prefixes(primes)
    mass_upper = PENALTY * (BLOCK_BUDGET + RESERVATION_BUDGET)
    for residue in range(1, (MODULUS + 1) // 2):
        opposite = MODULUS - residue
        block_length = 2 if residue == 1 else 58
        mass_upper += pair_bound(
            adjusted[residue - 1], adjusted[opposite - 1], block_length
        )
    assert mass_upper == 1_940_509_126_540 < 2 * SCALE
    print(f"Scaled mass bound for at most 294 primes: {small_support_upper}")
    print(f"Scaled mass bound with at most 57 additive choices: {mass_upper}")


if __name__ == "__main__":
    main()
