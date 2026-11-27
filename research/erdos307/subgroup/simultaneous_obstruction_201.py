"""Finite modular checks for the simultaneous obstruction modulo 3 × 67."""

from math import gcd, lcm

SMALL_PRIME = 3
LARGE_PRIME = 67
MODULUS = SMALL_PRIME * LARGE_PRIME
CLASS = 136
COUNT_PERIOD = lcm(MODULUS, LARGE_PRIME - 1)
COUNT = 1784
STARTING_SIZE = 33


def unit_product_and_sum(class_counts, modulus):
    product = 1
    reciprocal_sum = 0
    for residue, count in class_counts.items():
        product = product * pow(residue, count, modulus) % modulus
        reciprocal_sum = (reciprocal_sum + count * pow(residue, -1, modulus)) % modulus
    return product, reciprocal_sum


def satisfies_swap(total_product, total_reciprocal_sum, selected_size, modulus):
    product = pow(CLASS, selected_size, modulus)
    other_product = total_product * pow(product, -1, modulus) % modulus
    reciprocal_sum = selected_size * pow(CLASS, -1, modulus) % modulus
    other_sum = (total_reciprocal_sum - reciprocal_sum) % modulus
    return (
        product * reciprocal_sum % modulus == other_product
        and other_product * other_sum % modulus == product
    )


def main():
    assert COUNT_PERIOD == 4422
    assert (COUNT % 66, COUNT % 67) == (2, 42)
    assert (CLASS % SMALL_PRIME, CLASS % LARGE_PRIME) == (1, 2)
    assert gcd(CLASS, MODULUS) == 1

    base_product, base_sum = unit_product_and_sum({CLASS: COUNT}, MODULUS)
    assert base_product == 4
    cofactor = base_product * base_sum % MODULUS
    assert cofactor == 17
    selected_product = pow(CLASS, STARTING_SIZE, MODULUS)
    other_product = base_product * pow(selected_product, -1, MODULUS) % MODULUS
    assert (selected_product**2 % MODULUS, other_product**2 % MODULUS) == (1, 16)
    assert (selected_product**2 + other_product**2) % MODULUS == cofactor

    for modulus, selected_size in ((SMALL_PRIME, 7), (LARGE_PRIME, 1683)):
        assert 3 <= selected_size <= COUNT - 3
        assert selected_size % 2 == STARTING_SIZE % 2
        assert pow(CLASS, 2 * selected_size, modulus) == pow(CLASS, 2 * STARTING_SIZE, modulus)
        assert satisfies_swap(base_product % modulus, base_sum % modulus, selected_size, modulus)
    assert all(
        not satisfies_swap(base_product, base_sum, selected_size, MODULUS)
        for selected_size in range(COUNT_PERIOD)
    )

    square_order = 33
    character = {pow(4, power, LARGE_PRIME): power % SMALL_PRIME for power in range(square_order)}
    assert pow(4, square_order, LARGE_PRIME) == 1 and len(character) == square_order
    roots = [x for x in character if (x*x - cofactor*x + base_product**2) % LARGE_PRIME == 0]
    assert set(roots) == {1, 16}
    assert {character[x] for x in roots} == {0, 2}

    classes = {
        residue
        for residue in range(1, MODULUS)
        if gcd(residue, MODULUS) == 1
        and pow(residue, -1, SMALL_PRIME) == character[residue**2 % LARGE_PRIME]
    }
    assert CLASS in classes and len(classes) == 44
    for residue in classes:
        assert pow(residue, COUNT_PERIOD, MODULUS) == 1
        assert COUNT_PERIOD * pow(residue, -1, MODULUS) % MODULUS == 0
    padded_counts = {
        residue: COUNT if residue == CLASS else COUNT_PERIOD for residue in classes
    }
    assert unit_product_and_sum(padded_counts, MODULUS) == (base_product, base_sum)
    print("Common quadratic split, two separate swap witnesses, and 44-class obstruction verified.")


if __name__ == "__main__":
    main()
