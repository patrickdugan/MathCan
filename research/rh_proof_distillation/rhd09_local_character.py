"""Exact finite-ring model for the RHD-09 local character (not a Lean proof)."""
from __future__ import annotations
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

P = 29
P2 = P * P
COEFFS = (2, 14, -14, -2)
PHI20 = (1, 0, -1, 0, 1, 0, -1, 0, 1)


def poly_mul(a, b):
    v = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            v[i + j] += x * y
    return tuple(v)


def poly_product(polys):
    r = (1,)
    for p in polys:
        r = poly_mul(r, p)
    return r


def linear_solve(matrix, rhs):
    """Gauss-Jordan on square matrices in F_29."""
    n = len(rhs)
    M = [[x % P for x in row] + [rhs[i] % P] for i, row in enumerate(matrix)]
    for j in range(n):
        k = next((i for i in range(j, n) if M[i][j]), None)
        if k is None:
            raise ValueError('singular lift')
        M[j], M[k] = M[k], M[j]
        inv = pow(M[j][j], -1, P)
        M[j] = [x * inv % P for x in M[j]]
        for i in range(n):
            if i != j:
                t = M[i][j]
                M[i] = [(x - t * y) % P for x, y in zip(M[i], M[j])]
    return tuple(M[i][-1] for i in range(n))


def lifted_factors():
    """Simultaneous Hensel lift of Φ20's four quadratics modulo 29²."""
    fs = [(-1, c, 1) for c in COEFFS]
    base = poly_product(fs)
    assert all((a - b) % P == 0 for a, b in zip(base, PHI20))
    target = [((PHI20[i] - base[i]) // P) % P for i in range(8)]
    basis = []
    for j in range(4):
        other = poly_product(fs[:j] + fs[j + 1:])
        basis.extend([other + (0,), (0,) + other])
    mat = [[basis[col][i] for col in range(8)] for i in range(8)]
    sol = linear_solve(mat, target)
    lifts = tuple(((-1 + P * sol[2*j]) % P2,
                   (COEFFS[j] + P * sol[2*j+1]) % P2, 1) for j in range(4))
    assert all((a - b) % P2 == 0 for a, b in zip(poly_product(lifts), PHI20))
    return lifts


def norm(f, a, b):
    """Norm of a+bα for α²+f[1]α+f[0]=0 in Z/841[α]."""
    return (a*a - f[1]*a*b + f[0]*b*b) % P2


def theta(f, a, b):
    return (2*a - f[1]*b) % P


def principal_norm(f, a, b):
    return norm(f, 1+P*a, P*b)


def dirichlet_exponent(x):
    """Exponent of order-29 character; x↦-((x^28-1)/29) modulo 29."""
    x %= P2
    if gcd(x, P) != 1:
        raise ValueError('nonunit modulo 29²')
    z = pow(x, 28, P2)
    assert z % P == 1
    return (-((z-1)//P)) % P


def witness(f, a, b):
    n = principal_norm(f, a, b)
    t = theta(f, a, b)
    assert dirichlet_exponent(n) == t
    return {"a": a, "b": b, "theta": t, "norm_mod_841": n,
            "dirichlet_exponent": t, "local_match": True}


def training_records():
    for j, (c, f) in enumerate(zip(COEFFS, lifted_factors())):
        # Each f mod 29 has nonsquare discriminant, so the local residue degree is two.
        assert pow((c*c + 4) % P, 14, P) == P-1
        for a in range(P):
            for b in range(P):
                key = f'RHD09/{a}/{b}'.encode()
                bucket = int.from_bytes(hashlib.sha256(key).digest()[:4], 'big') % 10
                split = 'train' if bucket < 7 else 'val' if bucket < 9 else 'test'
                yield {"task": "local_norm_trace", "n": 20, "ell": P,
                       "factor_index": j, "factor_mod_29": [-1, c % P, 1],
                       "factor_mod_841": list(f), "split": split,
                       **witness(f, a, b), "lean_witness_proved": False,
                       "automorphic_witness_proved": False}


def write_data(output: Path):
    output.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    counts = {'train': 0, 'val': 0, 'test': 0}
    with output.open('wb') as stream:
        for r in training_records():
            line = (json.dumps(r, sort_keys=True, separators=(',', ':'))+'\n').encode()
            stream.write(line)
            digest.update(line)
            counts[r['split']] += 1
    manifest = {'dataset': 'RHD-09 finite principal-unit trace/norm',
                'sha256': digest.hexdigest(), 'examples': sum(counts.values()),
                'counts': counts, 'modulus': P2,
                'factors_mod_841': [list(f) for f in lifted_factors()],
                'theta_surjective_witness': {'a': 15, 'b': 0, 'value': 1},
                'dirichlet_character_order': 29,
                'norm_pullback_ramified_primes_above_29': 4,
                'other_primes_for_SphOffU_exception_set': 3,
                'proof_term_data': False}
    output.with_suffix('.manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_data(args.output), sort_keys=True))


if __name__ == '__main__':
    main()
