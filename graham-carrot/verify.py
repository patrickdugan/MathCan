"""Finite checks for MathCan/Graham-Carrot 02. Python standard library only."""
from math import gcd, isqrt

def primes(n):
    table = bytearray(b'\x01') * (n + 1)
    table[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if table[p]:
            table[p * p:n + 1:p] = b'\x00' * (((n - p * p) // p) + 1)
    return [i for i, flag in enumerate(table) if flag]

def is_prime(n):
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True

def local_roots(m, p):
    if p == 2:
        return 1
    d = gcd(3 ** m, p - 1)
    return 2 * d if pow(2, (p - 1) // d, p) == 1 else 0

def brute_roots(m, p):
    return sum(((pow(x, 3 ** m, p) - 4) *
                (pow(x, 3 ** m, p) - 2)) % p == 0 for x in range(p))

def twin_pairs(m, lo, hi):
    n = 3 ** m
    return [(x, x ** n - 4, x ** n - 2)
            for x in range(lo, hi + 1)
            if is_prime(x ** n - 4) and is_prime(x ** n - 2)]

def euler_product(m, cutoff):
    value = 1.
    for p in primes(cutoff):
        value *= (1 - local_roots(m, p)/p) / (1 - 1/p)**2
    return value

def test():
    ps = primes(500)
    assert all(local_roots(m, p) == brute_roots(m, p)
               for m in range(1, 7) for p in ps)
    assert twin_pairs(1, 2, 1000) == [
        (15, 3371, 3373), (201, 8120597, 8120599),
        (411, 69426527, 69426529),
        (477, 108531329, 108531331),
        (561, 176558477, 176558479)]
    for m in (1, 2, 3):
        print(f'm={m}, N={3**m}, Euler product p<=500: {euler_product(m, 500):.10f}')
    print('PASS: root-count identities and cubic twin pairs')

if __name__ == '__main__':
    test()
