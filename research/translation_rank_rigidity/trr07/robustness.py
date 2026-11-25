#!/usr/bin/env python3
"""V-E5: exact Hamming models and arithmetic representation controls.

For the function metric, the value at O is free and only S-values are charged.
For the table metric, every changed cell in S x S is charged independently.
Every result is a finite computation; no cryptographic complexity claim follows.
"""
import argparse
from collections import Counter
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import random
import time

from finite_fields import Field, Curve, Basis, prime, prime_factors, residue_profile


def kernel(F, rows, width):
    echelon = Basis(F)
    for row in rows:
        assert len(row) == width
        echelon.add(row)
    out = []
    for free in range(width):
        if free in echelon.rows:
            continue
        v = [0]*width
        v[free] = 1
        for i, row in sorted(echelon.rows.items(), reverse=True):
            v[i] = F.neg(F.sum(F.mul(row[j], v[j]) for j in range(i+1, width)))
        assert all(F.sum(F.mul(a,b) for a,b in zip(row,v)) == 0 for row in rows)
        out.append(v)
    return out, len(echelon)


def eval_space(C, seq):
    F=C.F; d=len(seq)//3; U=Basis(F)
    for a in range(d+1):
        for b in range(d+1-a):
            U.add([F.mul(F.pow(x,a),F.pow(y,b)) for x,y in seq[1:]])
    assert len(U) == len(seq)-2
    return U


def translated_distance(F, seq, lam, enumeration_limit=500000, support_limit=3):
    n=len(seq)
    # B g = (M_g|S) lambda. Each column corresponds to one value g(sT).
    B=[[lam[(s-i)%n] for s in range(n)] for i in range(1,n)]
    null, rank=kernel(F,B,n)
    assert all(F.sum(row)==0 for row in B)
    fixed, fixed_rank=kernel(F,B+[[1]+[0]*(n-1)],n)
    assert fixed_rank==rank+1 and len(fixed)==len(null)-1
    f=[0]+[P[0] for P in seq[1:]]
    best=n-1; best_g=None
    search_size=F.q**len(fixed)
    examined=0
    if search_size<=enumeration_limit:
        for coeffs in product(range(F.q),repeat=len(fixed)):
            h=[F.sum(F.mul(c,v[i]) for c,v in zip(coeffs,fixed)) for i in range(n)]
            differences=Counter(F.sub(f[i],h[i]) for i in range(1,n))
            c,agree=min(differences.items(),key=lambda z:(-z[1],z[0]))
            dist=n-1-agree
            if dist<best:
                best=dist; best_g=[F.add(c,a) for a in h]
            examined+=1
        status="exact"
        lower=best
    else:
        # Exhaust supports, solving their linear syndromes exactly. The free O
        # column permits every assigned pole value throughout this search.
        cols=[[row[s] for row in B] for s in range(n)]
        target=[F.neg(F.sum(F.mul(a,b) for a,b in zip(row,f))) for row in B]
        lower=support_limit+1; status="bounded"
        found=False
        for k in range(support_limit+1):
            for support in combinations(range(1,n),k):
                span=Basis(F); span.add(cols[0])
                for s in support:span.add(cols[s])
                examined+=1
                if span.contains(target):
                    best=lower=k; status="exact_support_search"; found=True; break
            if found:break
        if not found:
            c,agree=min(Counter(f[1:]).items(),key=lambda z:(-z[1],z[0]))
            best=n-1-agree;best_g=[c]*n
    if best_g is not None:
        assert all(F.sum(F.mul(a,b) for a,b in zip(row,best_g))==0 for row in B)
        assert sum(a!=b for a,b in zip(best_g[1:],f[1:]))==best
    return dict(status=status,syndrome_rank=rank,admissible_function_dimension=len(null),
                normalized_search_size=search_size,examined=examined,
                distance_lower=lower,distance_upper=best,witness=best_g,
                metric="Hamming on S; g(O) is uncharged")


def one_case(C,seq):
    F=C.F;n=len(seq);constant,ratios,lam=residue_profile(C,seq,complete=True)
    U=eval_space(C,seq);values=[0]+[P[0] for P in seq[1:]]
    M=[[values[(i+j)%n] for j in range(1,n)] for i in range(1,n)]
    syndrome=[F.sum(F.mul(a,b) for a,b in zip(row,lam[1:])) for row in M]
    diag=[F.neg(F.div(a,b)) for a,b in zip(syndrome,lam[1:])]
    corrected=[row[:] for row in M]
    for i,e in enumerate(diag):corrected[i][i]=F.add(corrected[i][i],e)
    assert all(U.contains(row) for row in corrected)
    assert all(corrected[i][j]==corrected[j][i] for i in range(n-1) for j in range(n-1))
    changed=sum(e!=0 for e in diag)
    assert changed<=n-1
    by_sum={}
    for i in range(1,n):
        for j in range(1,n):by_sum.setdefault((i+j)%n,set()).add(corrected[i-1][j-1])
    is_translation_table=all(len(v)==1 for v in by_sum.values())
    rational_pairs=0;doublings=0;inverse_pairs=0
    for P in seq[1:]:
        for Q in seq[1:]:
            x,y=P;u,v=Q;R=C.add(P,Q)
            if x!=u:
                assert R is not None
                lhs=F.mul(F.add(F.add(R[0],x),u),F.pow(F.sub(u,x),2))
                assert lhs==F.pow(F.sub(v,y),2)
                rational_pairs+=1
            elif P==Q:
                assert R is not None
                lhs=F.mul(F.add(R[0],F.mul(F.const(2),x)),F.pow(F.mul(F.const(2),y),2))
                rhs=F.pow(F.add(F.mul(F.const(3),F.pow(x,2)),C.a),2)
                assert lhs==rhs;doublings+=1
            else:
                assert R is None;inverse_pairs+=1
    scalar_checks=[]
    for bits in [8,32,64,128,256]:
        k=(1<<bits)-1;P=seq[1];R=None;Q=P;z=k;adds=0;doubles=0
        while z:
            if z&1:R=C.add(R,Q);adds+=1
            Q=C.add(Q,Q);doubles+=1;z>>=1
        assert R==seq[k%n]
        scalar_checks.append(dict(scalar_bits=bits,additions=adds,doublings=doubles))
    # An exact straight-line program with s multiplications represents X^(2^s).
    power_checks=[]
    for s in [1,4,16,64,256]:
        a=seq[1][0] or F.const(2);value=a
        for _ in range(s):value=F.mul(value,value)
        assert value==F.pow(a,1<<s)
        power_checks.append(dict(multiplications=s,formal_polynomial_degree=str(1<<s)))
    distance=translated_distance(F,seq,lam)
    if distance['witness'] is not None:
        g=distance['witness']
        assert all(U.contains([g[(i+j)%n] for j in range(1,n)]) for i in range(1,n))
        distance['witness_direct_matrix_verified']=True
    rng=random.Random(20261125+F.q*1000+n)
    for _ in range(8):
        random_even=[rng.randrange(F.q) for _ in range((n+1)//2)]
        random_even += list(reversed(random_even[1:]))
        table=[[random_even[(i+j)%n] for j in range(1,n)] for i in range(1,n)]
        direct=all(U.contains(row) for row in table)
        residual=all(F.sum(F.mul(a,b) for a,b in zip(row,lam[1:]))==0 for row in table)
        assert direct==residual
    arbitrary=[[rng.randrange(F.q) for _ in range(n-1)] for _ in range(n-1)]
    for i in range(n-1):
        for j in range(i):arbitrary[i][j]=arbitrary[j][i]
    for i,row in enumerate(arbitrary):
        residual=F.sum(F.mul(a,b) for a,b in zip(row,lam[1:]))
        arbitrary[i][i]=F.sub(arbitrary[i][i],F.div(residual,lam[i+1]))
    assert all(U.contains(row) for row in arbitrary)
    return dict(field=F.metadata(),a=C.a,b=C.b,curve_order=C.order,subgroup_order=n,
                generator=seq[1],subgroup=seq,assigned_pole_value=0,
                lower_degree=n//3,lower_degree_value=constant,residue_ratios=ratios,
                table=dict(changed_cells=changed,total_cells=(n-1)**2,
                           diagonal_correction=diag,corrected_contains=True,
                           corrected_is_translation_table=is_translation_table),
                function=distance,
                calibration_controls=dict(random_even_functions=8,arbitrary_symmetric_matrices=1),
                rational_addition_control=dict(distinct_x_pairs=rational_pairs,
                      doubling_pairs=doublings,inverse_pairs=inverse_pairs),
                scalar_multiplication_control=scalar_checks,repeated_squaring_control=power_checks)


def signed_orbit(q,n):
    if q%n==0:return "matching"
    seen={1,n-1};v=q%n
    while v not in seen:
        seen.add(v);seen.add((-v)%n);v=v*q%n
    return "transitive" if len(seen)==n-1 else "nontransitive"


def fixtures():
    targets=[5,7,11,13,17,19,23,29,31]
    chosen={}
    F=Field(11);C=Curve(F,2,9)
    chosen[(5,"known_exception")]=(C,C.sequence((4,2),5))
    for p in range(5,102):
        if not prime(p):continue
        F=Field(p)
        for a,b in product(range(min(p,7)),repeat=2):
            if (4*a**3+27*b*b)%p==0:continue
            C=Curve(F,a,b)
            for n in prime_factors(C.order):
                if n not in targets:continue
                key=(n,signed_orbit(p,n))
                if key in chosen:continue
                chosen[key]=(C,next(C.subgroups(n)))
    for p,e in [(5,2),(7,2),(11,2)]:
        F=Field(p,e)
        for a,b in [(0,1),(1,0),(1,1),(F.p,1),(1,F.p)]:
            try:C=Curve(F,a,b)
            except AssertionError:continue
            for n in prime_factors(C.order):
                if n not in targets:continue
                key=(n,f"extension_{p}_{e}")
                if key not in chosen:chosen[key]=(C,next(C.subgroups(n)))
    return chosen


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='robustness.json');args=ap.parse_args()
    start=time.monotonic();rows=[]
    for label,(C,seq) in sorted(fixtures().items()):
        row=one_case(C,seq);row['cohort']=list(label);rows.append(row)
        print(json.dumps(dict(cohort=label,table_changes=row['table']['changed_cells'],
                   function_distance=[row['function']['distance_lower'],row['function']['distance_upper']],
                   function_status=row['function']['status'])),flush=True)
    assert any(row['lower_degree_value'] is not None and row['subgroup_order']==5 for row in rows)
    receipt=dict(schema='trr07-robustness-v1',rows=rows,cases=len(rows),
                 all_diagonal_corrections_verified=True,
                 exact_function_distances=sum(r['function']['status'].startswith('exact') for r in rows),
                 elapsed_seconds=time.monotonic()-start,
                 source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('finite_fields.py')]},
                 scope='Exact finite tests of two specified Hamming metrics and arithmetic controls; no circuit lower bound.')
    out=Path(args.out);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='rows'},sort_keys=True))


if __name__=='__main__':main()
