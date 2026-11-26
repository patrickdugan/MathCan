#!/usr/bin/env python3
"""Exact finite checks for polynomial-decoder translation-rank bounds.

Standard library only.  Produces deterministic JSON.  Experiments concern
finite matrices and do not infer cryptographic computational hardness.
"""
from collections import Counter
from itertools import product
from math import comb
import json
import random
from pathlib import Path
from hashlib import sha256


def rank_mod(matrix, p):
    a = [list(row) for row in matrix]
    rows, cols = len(a), len(a[0]) if a else 0
    pivot = 0
    for j in range(cols):
        q = next((i for i in range(pivot, rows) if a[i][j] % p), None)
        if q is None:
            continue
        a[pivot], a[q] = a[q], a[pivot]
        inv = pow(a[pivot][j] % p, -1, p)
        a[pivot][j:] = [(v * inv) % p for v in a[pivot][j:]]
        for i in range(pivot + 1, rows):
            z = a[i][j] % p
            if z:
                a[i][j:] = [(x-z*y) % p for x,y in zip(a[i][j:], a[pivot][j:])]
        pivot += 1
        if pivot == rows:
            break
    return pivot


def rank_binary(rows):
    pivots = {}
    for row in rows:
        while row:
            bit = row.bit_length() - 1
            if bit in pivots:
                row ^= pivots[bit]
            else:
                pivots[bit] = row
                break
    return len(pivots)


def is_prime(n):
    return n > 1 and all(n % k for k in range(2, int(n**0.5)+1))


def reduced_monomials(r, d, p):
    if d < 0:
        return []
    return [a for a in product(range(min(d,p-1)+1), repeat=r) if sum(a) <= d]


def total_degree_bound(r, s, d, p):
    return min(len(reduced_monomials(r,k-1,p)) + len(reduced_monomials(s,d-k,p))
               for k in range(d+2))


def value_monomial(point, exponent, p):
    z = 1
    for a,e in zip(point,exponent):
        z = z * pow(a,e,p) % p
    return z


def cyclic_examples():
    out = []
    # Each (N,p,r,D) has N prime, p prime, N | p-1, and distinct
    # base-(D+1) monomial exponents below N.
    specs = [(7,29,1,4),(13,53,2,2),(23,47,2,4),
             (31,311,3,2),(61,367,3,3),(61,367,4,2),
             (193,773,4,3),(101,607,3,4)]
    for n,p,r,d in specs:
        assert is_prime(n) and is_prime(p) and (p-1) % n == 0
        zeta = next(pow(z,(p-1)//n,p) for z in range(2,p)
                    if pow(z,(p-1)//n,p) != 1)
        assert pow(zeta,n,p) == 1
        weights = [(d+1)**j for j in range(r)]
        exponents = [sum(a*w for a,w in zip(alpha,weights))
                     for alpha in reduced_monomials(r,d,p)]
        assert len(set(exponents)) == len(exponents) == comb(r+d,d)
        assert max(exponents) < n
        values = [sum(pow(zeta,e*x,p) for e in exponents) % p for x in range(n)]
        matrix = [[values[(x+y)%n] for y in range(n)] for x in range(n)]
        rank = rank_mod(matrix,p)
        assert rank == len(exponents)
        # Independently check the stated decoder on every pair.
        encodings = [[pow(zeta,w*x,p) for w in weights] for x in range(n)]
        monomials = reduced_monomials(r,d,p)
        for x in range(n):
            left = [value_monomial(encodings[x],a,p) for a in monomials]
            for y in range(n):
                decoded = sum(u*value_monomial(encodings[y],a,p)
                              for u,a in zip(left,monomials)) % p
                assert decoded == matrix[x][y]
        out.append(dict(group_order=n,field_prime=p,latent_dimension=r,
                        degree_per_block=d,total_degree=2*d,root=zeta,
                        exponent_weights=weights,largest_exponent=max(exponents),
                        rank=rank,monomial_bound=comb(r+d,d),
                        verified_pairs=n*n))
    return out


def additive_total_degree_examples():
    rng = random.Random(20261125)
    out = []
    for p,r,d in [(7,2,d) for d in range(1,6)] + [(5,3,d) for d in range(1,5)]:
        points = list(product(range(p),repeat=r))
        lookup = {x:i for i,x in enumerate(points)}
        addition = [[lookup[tuple((a+b)%p for a,b in zip(x,y))] for y in points]
                    for x in points]
        exponents = [a for a in reduced_monomials(r,d,p) if sum(a)==d]
        evals = [[value_monomial(x,a,p) for a in exponents] for x in points]
        target = total_degree_bound(r,r,d,p)
        for attempt in range(1,129):
            coefficients = [rng.randrange(p) for _ in exponents]
            values = [sum(c*m for c,m in zip(coefficients,row))%p for row in evals]
            matrix = [[values[z] for z in row] for row in addition]
            rank = rank_mod(matrix,p)
            if rank == target:
                break
        assert rank == target, (p,r,d,rank,target)
        out.append(dict(field_prime=p,group_dimension=r,group_order=p**r,
                        total_degree=d,rank=rank,bound=target,trials=attempt,
                        homogeneous_coefficients=[dict(exponent=list(a),coefficient=c)
                                                  for a,c in zip(exponents,coefficients) if c]))
    return out


def binary_exhaustive():
    out = []
    for r,d in [(3,2),(4,2),(4,3)]:
        n=2**r
        monomial_masks=[m for m in range(n) if m.bit_count()<=d]
        monomial_words=[sum(1<<x for x in range(n) if x&m==m) for m in monomial_masks]
        # Enumerate polynomial coefficient vectors in Gray order.
        word=0
        hist=Counter()
        witness={}
        for step in range(1<<len(monomial_words)):
            if step:
                j=(step & -step).bit_length()-1
                word ^= monomial_words[j]
            translates=[sum(((word >> (x^y)) & 1)<<y for y in range(n)) for x in range(n)]
            rank=rank_binary(translates)
            hist[rank]+=1
            witness.setdefault(rank,word)
        maximum=max(hist)
        bound=total_degree_bound(r,r,d,2)
        expected={(3,2):4,(4,2):6,(4,3):8}[r,d]
        assert maximum==expected
        out.append(dict(field_prime=2,group_dimension=r,group_order=n,total_degree=d,
                        polynomial_count=1<<len(monomial_words),
                        maximum_translation_rank=maximum,total_degree_bound=bound,
                        rank_histogram=dict(sorted(hist.items())),
                        maximizing_word=witness[maximum]))
    return out


def rational_cauchy_examples():
    out=[]
    for n,p in ((7,29),(13,53),(23,47)):
        zeta=next(pow(z,(p-1)//n,p) for z in range(2,p)
                  if pow(z,(p-1)//n,p)!=1)
        group=[pow(zeta,j,p) for j in range(n)]
        a=next(z for z in range(1,p) if z not in group)
        matrix=[[pow((x*y-a)%p,-1,p) for y in group] for x in group]
        rank=rank_mod(matrix,p)
        assert rank==n
        out.append(dict(field_prime=p,group_order=n,a=a,
                        rank=rank,latent_dimension_per_block=1,
                        denominator_total_degree=2))
    return out


if __name__=='__main__':
    result=dict(schema='strategy-v-decoder-sharpness-v1',
                arithmetic='exact prime-field elimination and binary XOR elimination',
                cyclic_separate_degree=cyclic_examples(),
                additive_total_degree=additive_total_degree_examples(),
                binary_exhaustive=binary_exhaustive(),
                rational_cauchy=rational_cauchy_examples())
    result['counts']=dict(cyclic_examples=len(result['cyclic_separate_degree']),
                         cyclic_decoder_pairs=sum(x['verified_pairs'] for x in result['cyclic_separate_degree']),
                         additive_examples=len(result['additive_total_degree']),
                         exhaustive_binary_polynomials=sum(x['polynomial_count'] for x in result['binary_exhaustive']))
    result['source_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_name('decoder_receipt.json').write_text(
        json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))
