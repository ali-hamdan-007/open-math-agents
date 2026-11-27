from math import gcd, isqrt, lcm

LIMIT = 1000000
SCALE = 10**12
sieve = bytearray(b'\1') * (LIMIT + 1)
sieve[0:2] = b'\0\0'
for p in range(2, isqrt(LIMIT) + 1):
    if sieve[p]:
        sieve[p*p::p] = bytes((LIMIT - p*p)//p + 1)
primes = [p for p in range(3, LIMIT + 1, 2) if sieve[p]]

def order(value, modulus):
    power, exponent = value % modulus, 1
    while power != 1:
        power = power * value % modulus
        exponent += 1
    return exponent

for modulus in range(9, 151, 2):
    if sieve[modulus] or any(modulus % (p*p) == 0 for p in range(3, isqrt(modulus) + 1, 2)):
        continue
    steps = [lcm(2, order(r*r, modulus)) for r in range(1, modulus) if gcd(r, modulus) == 1]
    if not all(gcd(d, modulus) == 1 for d in steps):
        print(modulus, 'fails unit-step condition')
        continue
    threshold = 7 + max(steps)*(modulus - 2) + 2*sum(d-1 for d in steps)
    eligible = [p for p in primes if modulus % p][:threshold - 1]
    assert len(eligible) == threshold - 1
    upper = sum((SCALE + p - 1)//p for p in eligible)
    lower = sum(SCALE//p for p in eligible)
    status = 'below 2' if upper < 2*SCALE else 'above 2' if lower >= 2*SCALE else 'indeterminate'
    print(modulus, max(steps), threshold, lower, upper, status)
