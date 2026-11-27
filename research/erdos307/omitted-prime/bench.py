"""Compare modular sieve kernels on identical, reproducible field residues."""
from random import Random
from time import perf_counter

def paired(c, n, p):
    exponent = (p - 1) // 2
    return pow((c + 2*n) % p, exponent, p) in (0, 1) and \
        pow((c - 2*n) % p, exponent, p) in (0, 1)

def dickson(c, n, p):
    k = (p - 1) // 2
    z = n*n % p
    a, b, t = 2, c, 1
    for bit in bin(k)[2:]:
        middle = (a*b-c*t) % p
        if bit == "0":
            a, b, t = (a*a-2*t) % p, middle, t*t % p
        else:
            a, b, t = middle, (b*b-2*z*t) % p, z*t*t % p
    return a == 2

if __name__ == "__main__":
    rng = Random(307)
    for p in (5, 7, 101, 1009, 65537):
        squares = {x*x % p for x in range(p)}
        def lookup(c, n, p):
            return (c + 2*n) % p in squares and (c - 2*n) % p in squares
        cases = [(rng.randrange(p), rng.randrange(1, p), p) for _ in range(100000)]
        if p <= 101:
            for c in range(p):
                for n in range(1, p):
                    assert paired(c,n,p) == dickson(c,n,p) == lookup(c,n,p)
        baseline = [lookup(*case) for case in cases]
        for fn in (paired, dickson, lookup):
            start = perf_counter()
            actual = [fn(*case) for case in cases]
            elapsed = perf_counter() - start
            assert actual == baseline
            print(f"{p:5} {fn.__name__:8} {elapsed:.4f}s")
