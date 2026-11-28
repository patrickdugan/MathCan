"""Exact branch-count lattices and constructive quadratic-sign parameters."""
from dataclasses import dataclass
from math import gcd, isqrt, lcm, prod


@dataclass(frozen=True)
class BranchLattice:
    modulus: int
    triple_stride: int
    halving_residue: int
    halving_period: int

    @property
    def index(self) -> int:
        return self.triple_stride * self.halving_period

    def contains(self, u: int, A: int) -> bool:
        return (u % self.triple_stride == 0 and
                (A - (u // self.triple_stride) * self.halving_residue)
                % self.halving_period == 0)


def branch_lattice(modulus: int, *, max_order: int = 2_000_000) -> BranchLattice:
    """Return basis (h,s),(0,L) of { (u,A): 2^A == 3^u mod m }.

    General odd composite moduli are allowed. A finite group calculation finds
    L=ord_m(2), then the least positive h with 3^h in <2> and 3^h=2^s.
    Complexity O(L+h); the explicit cap prevents accidental large allocations.
    """
    if type(modulus) is not int or modulus < 1 or gcd(modulus, 6) != 1:
        raise ValueError("modulus must be positive and coprime to 6")
    if modulus == 1:
        return BranchLattice(1, 1, 0, 1)
    powers = {1: 0}
    x = 2 % modulus
    L = 1
    while x != 1:
        if L >= max_order:
            raise ValueError("order of 2 exceeds the declared computation budget")
        powers[x] = L
        x = x * 2 % modulus
        L += 1
    y, h = 3 % modulus, 1
    while y not in powers:
        if h >= max_order:
            raise ValueError("quotient order of 3 exceeds computation budget")
        y = y * 3 % modulus
        h += 1
    return BranchLattice(modulus, h, powers[y], L)


def combine_congruences(a: int, m: int, b: int, n: int) -> tuple[int, int]:
    """Generalized CRT for x=a mod m and x=b mod n."""
    common = gcd(m, n)
    if (b - a) % common:
        raise ValueError("inconsistent congruences")
    reduced = n // common
    step = 0 if reduced == 1 else ((b-a)//common * pow(m//common, -1, reduced)) % reduced
    period = lcm(m, n)
    return (a + m * step) % period, period


def primitive_prime_lattice(primes: tuple[int, ...]) -> tuple[BranchLattice, tuple[int, ...]]:
    """Squarefree CRT construction, checking primality and primitive base 2."""
    if not primes or len(set(primes)) != len(primes):
        raise ValueError("distinct primes are required")
    logs = []
    for p in primes:
        if not is_prime(p) or p <= 3:
            raise ValueError("all factors must be primes greater than 3")
        values = {}
        x = 1
        for i in range(p - 1):
            if x in values:
                raise ValueError("2 is not a primitive root at a factor")
            values[x] = i
            x = x * 2 % p
        if x != 1 or 3 not in values:
            raise ValueError("invalid unit-group certificate")
        logs.append(values[3])
    stride = 1
    for i, p in enumerate(primes):
        for j in range(i):
            common = gcd(p - 1, primes[j] - 1)
            stride = lcm(stride, common // gcd(common, logs[i] - logs[j]))
    residue, period = 0, 1
    for p, logarithm in zip(primes, logs):
        residue, period = combine_congruences(residue, period, stride * logarithm, p - 1)
    return BranchLattice(prod(primes), stride, residue, period), tuple(logs)


def is_prime(n: int) -> bool:
    return type(n) is int and n >= 2 and all(n % q for q in range(2, isqrt(n) + 1))


def legendre(n: int, p: int) -> int:
    if not is_prime(p) or p == 2:
        raise ValueError("p must be an odd prime")
    value = pow(n, (p - 1) // 2, p)
    return -1 if value == p - 1 else value


def construct_sign_parameters(seeds: tuple[int, ...], *, prime_bound: int = 1_000_000) -> tuple[int, ...]:
    """Find one p_i == 1 mod24 per seed prime, with a diagonal negative sign.

    Exhaustion raises an error; Dirichlet guarantees existence without a bound.
    The bounded implementation itself makes no search-time guarantee.
    """
    if not seeds or len(set(seeds)) != len(seeds) or any(q <= 3 or not is_prime(q) for q in seeds):
        raise ValueError("seeds must be distinct primes greater than 3")
    result = []
    for i in range(len(seeds)):
        for p in range(25, prime_bound + 1, 24):
            if p in result or p in seeds or not is_prime(p):
                continue
            if all(legendre(q, p) == (-1 if i == j else 1) for j, q in enumerate(seeds)):
                result.append(p)
                break
        else:
            raise ValueError("no prescribed prime found within prime_bound")
    return tuple(result)


def near_resonances(lattice: BranchLattice, u_max: int, tolerance: int, slope: int = 6) -> list[tuple[int, int]]:
    """Enumerate positive-u lattice points in a frozen finite slope window."""
    if u_max < 1 or tolerance < 0 or slope < 2:
        raise ValueError("invalid resonance search bounds")
    result = []
    for u in range(lattice.triple_stride, u_max + 1, lattice.triple_stride):
        lower = max(2 * u, slope * u - tolerance)
        upper = slope * u + tolerance
        residue = (u // lattice.triple_stride * lattice.halving_residue) % lattice.halving_period
        first = lower + (residue - lower) % lattice.halving_period
        result.extend((u, A) for A in range(first, upper + 1, lattice.halving_period))
    return result
