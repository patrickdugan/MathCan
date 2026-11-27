"""DETFACT-15: independent finite checks of streamed power and packing."""
import json
import math
import random


def execute(a, n, factors):
    x = a % n
    for q in factors:
        x = pow(x, q, n)
    return x


def primes(k):
    sieve = bytearray(b'\1') * (k + 1)
    sieve[:2] = b'\0\0'
    for p in range(2, math.isqrt(k) + 1):
        if sieve[p]:
            sieve[p*p:k+1:p] = b'\0' * ((k-p*p)//p+1)
    return [p for p in range(3, k+1, 2) if sieve[p]]


def maximal_powers(k):
    pairs = []
    for p in primes(k):
        q = p
        while q <= k // p:
            q *= p
        assert p <= q <= k < p*q and k < q*q
        pairs.append((p, q))
    return pairs


def chunks(powers, w, segment=None):
    """Conservative packing with optional flush at each segment boundary."""
    out = []
    c = 1
    current = None
    for p, q in powers:
        group = (p - 3) // (2 * segment) if segment else 0
        if current is not None and group != current and c != 1:
            out.append(c)
            c = 1
        current = group
        if c != 1 and c.bit_length() + q.bit_length() > w:
            out.append(c)
            c = 1
        if q.bit_length() > w:
            out.append(q)
        else:
            c *= q
            assert c.bit_length() <= w
    if c != 1:
        out.append(c)
    return out


def audit():
    rng = random.Random(1501)
    r = dict(schema='DETFACT-15-exact', streamed=0, checkpoint=0,
             equal_product=0, split_probe=0, nonunit_cases=0,
             maximal_powers=0, singleton_checks=0, negative_controls=0)
    for i in range(600):
        n = [1, 2, 3, 15, 45, 77, 143, 65537, 2**64-59][i % 9]
        a = [0, 1, 2, 3, 5, n, n+1, rng.randrange(0, 2*n+1)][i % 8]
        f = [rng.randrange(0, 33) for _ in range(i % 9)]
        explicit = math.prod(f)
        x = execute(a, n, f)
        assert x == pow(a, explicit, n)
        r['streamed'] += 1
        r['nonunit_cases'] += int(math.gcd(a, n) != 1)
        for k in range(len(f)+1):
            assert execute(execute(a, n, f[:k]), n, f[k:]) == x
            r['checkpoint'] += 1
        merged = [math.prod(f[:len(f)//2]), math.prod(f[len(f)//2:])]
        assert execute(a, n, merged) == x
        r['equal_product'] += 1
        for j in range(9):
            y = pow(a, explicit * (1 << j), n)
            assert x == y and math.gcd(abs(x-1), n) == math.gcd(abs(y-1), n)
            r['split_probe'] += 1
            x = x*x % n
    for t in [1, 2, 3, 4, 5, 6, 7, 8, 9]:
        k = 1 << (2*t)
        for k1 in [k, k+1]:
            ps = maximal_powers(k1)
            r['maximal_powers'] += len(ps)
            assert all(q.bit_length() > t for _, q in ps)
            expected = [q for _, q in ps]
            for segment in [None, 1, 32, 257]:
                assert chunks(ps, 2*t, segment) == expected
                r['singleton_checks'] += 1
    # Check that the sufficient threshold is not necessary:
    # below 65536 packing can still produce singleton execution.
    for k in [65535, 65536, 65537]:
        ps = maximal_powers(k)
        cs = chunks(ps, 16, 32)
        for n in [15, 77, 1009]:
            assert execute(2, n, cs) == execute(2, n, [q for _, q in ps])
            r['equal_product'] += 1
    # Small K permits packing, so a universal singleton claim is false.
    assert chunks(maximal_powers(7), 16) != [q for _, q in maximal_powers(7)]
    r['negative_controls'] += 1
    # Omitting a prime power changes the result in this fixture.
    assert execute(2, 23, [9, 5, 7]) != execute(2, 23, [3, 5, 7])
    r['negative_controls'] += 1
    # A forged checkpoint is outside the checkpoint theorem's premise.
    assert execute(2, 15, [3, 5]) != execute(1, 15, [5])
    r['negative_controls'] += 1
    return r


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2, sort_keys=True))
