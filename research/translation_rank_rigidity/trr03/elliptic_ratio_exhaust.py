"""Exact search for constant ratios in the elliptic decoder obstruction.

Uses elliptic_decoder_probe.py from the same directory.
"""
from elliptic_decoder_probe import Curve, Basis, prime
from itertools import product
from collections import Counter
from pathlib import Path
import json
import argparse
import hashlib


def mul(C,k,P):
    out=None
    while k:
        if k&1:out=C.add(out,P)
        P=C.add(P,P);k>>=1
    return out


def subgroup_sequences(C,n):
    seen=set()
    for P in C.points[1:]:
        if P in seen or mul(C,n,P) is not None:continue
        seq=[None];Q=P
        for _ in range(n-1):
            seq.append(Q);seen.add(Q);Q=C.add(Q,P)
        assert Q is None and len(set(seq))==n
        yield seq


def ratios(C,seq):
    p=C.p;n=len(seq);m=(n-1)//2
    roots=[seq[j][0] for j in range(1,m+1)]
    assert len(set(roots))==m
    derivatives={x:1 for x in roots}
    for x in roots:
        for t in roots:
            if t!=x:derivatives[x]=derivatives[x]*(x-t)%p
    lam=[0]+[pow(2*y*derivatives[x]%p,-1,p) for x,y in seq[1:]]
    assert all((lam[j]+lam[n-j])%p==0 for j in range(1,n))
    f=[0]+[x for x,y in seq[1:]]
    ratios=[]
    for q in range(1,n):
        numer=sum(f[(j+q)%n]*lam[j] for j in range(1,n))%p
        ratios.append(numer*pow(lam[q],-1,p)%p)
        if len(ratios)>1 and ratios[-1]!=ratios[0]:
            return None,ratios,lam
    return ratios[0],ratios,lam


def pm_order(p,n):
    if p%n==0:return None
    a=p%n;seen={1,n-1};v=a
    while v not in seen:
        seen.add(v);seen.add((-v)%n);v=v*a%n
    return len(seen)


def tate5_parameters(C,P):
    p=C.p;u,v=P
    slope=(3*u*u+C.a)*pow(2*v,-1,p)%p
    a2=(3*u-slope*slope)%p
    assert a2
    kappa=2*v*pow(a2,-1,p)%p
    t=-a2*pow(kappa*kappa%p,-1,p)%p
    assert (1-2*slope*pow(kappa,-1,p))%p==t
    discriminant=pow(t,5,p)*(t*t-11*t-1)%p
    assert discriminant
    c=(u+kappa*kappa*t*t)%p
    return dict(parameter=t,kappa=kappa,slope=slope,
                parameter_equation=(t*t-t-1)%p,assigned_value=c)


def critical_contains(C,seq,c):
    p=C.p;n=len(seq);d=n//3;points=seq[1:]
    basis=Basis(p)
    for i in range(d+1):
        for j in range(d+1-i):
            basis.add([pow(x,i,p)*pow(y,j,p)%p for x,y in points])
    assert len(basis)==n-2
    matrix=C.mat(points,c)
    return all(basis.contains(row) for row in matrix)


def first_witness():
    C=Curve(11,2,9);T=(4,2);seq=[None]
    for j in range(1,5):seq.append(mul(C,j,T))
    features=[(9,0)]+seq[1:]
    values=[9]+[P[0] for P in seq[1:]]
    for i in range(5):
        for j in range(5):
            P,Q=seq[i],seq[j]
            R=C.add(P,Q)
            expected=9 if R is None else R[0]
            x,y=features[i];u,v=features[j]
            assert (5*x*u+4*y*v)%11==expected==values[(i+j)%5]
    assert (0-(9**3+2*9+9))%11
    rank=Basis(11)
    for row in C.mat(seq,9):rank.add(row)
    assert len(rank)==2
    return dict(p=11,a=2,b=9,curve_order=15,subgroup_order=5,
                generator=list(T),subgroup=seq,assigned_value=9,
                assigned_feature_at_identity=[9,0],
                decoder='5*x(P)*x(Q)+4*y(P)*y(Q) mod 11',
                verified_pairs=25,full_translation_rank=2,
                tate5=tate5_parameters(C,T))


def run(maxp,limit_per_p=0):
    rows=[];exceptions=[];counts=Counter();negative_checks=[]
    for p in range(5,maxp+1):
        if not prime(p):continue
        local=Counter();checked_negative=False
        for a,b in product(range(p),repeat=2):
            if limit_per_p and a*p+b>=limit_per_p:break
            if (4*a**3+27*b*b)%p==0:continue
            C=Curve(p,a,b);N=len(C.points);local['curves']+=1
            assert (N-p-1)**2<=4*p
            for n in range(5,N+1):
                if N%n or not prime(n):continue
                for seq in subgroup_sequences(C,n):
                    local['subgroups']+=1
                    local['full_prime_groups' if n==N else 'proper_prime_subgroups']+=1
                    if n==p:local['characteristic_order_subgroups']+=1
                    elif pm_order(p,n)==n-1:local['transitive_tame']+=1
                    else:local['nontransitive_tame']+=1
                    c,rat,lam=ratios(C,seq)
                    tate=None
                    if n==5:
                        local['order5_subgroups']+=1
                        tate=tate5_parameters(C,seq[1])
                        assert (c is not None)==(tate['parameter_equation']==0)
                    if c is not None:
                        local['exceptions']+=1
                        assert critical_contains(C,seq,c)
                        local['direct_positive_matrix_checks']+=1
                        local['direct_positive_entries']+=(n-1)**2
                        if tate:
                            assert c==tate['assigned_value']
                            j=1728*4*a**3*pow((4*a**3+27*b*b)%p,-1,p)%p
                            assert j==(-25*pow(2,-1,p))%p
                        witness=dict(p=p,a=a,b=b,curve_order=N,subgroup_order=n,
                                     generator=seq[1],constant=c,ratios=rat,
                                     subgroup=seq,annihilator=lam,
                                     signed_frobenius_orbit_size=pm_order(p,n),
                                     tate5=tate)
                        exceptions.append(witness)
                    elif not checked_negative:
                        # Independent direct-matrix check of every possible
                        # assigned pole value on one negative group per field.
                        assert not any(critical_contains(C,seq,value) for value in range(p))
                        local['direct_negative_matrix_checks']+=p
                        local['direct_negative_entries']+=p*(n-1)**2
                        negative_checks.append(dict(p=p,a=a,b=b,curve_order=N,
                                                    subgroup_order=n,generator=seq[1],
                                                    values_exhausted=p,
                                                    first_unequal_ratios=rat))
                        checked_negative=True
        row=dict(p=p,**dict(local));rows.append(row);counts.update(local)
    result=dict(schema='elliptic-ratio-exhaust-v1',max_field_prime=maxp,
                limit_curve_coefficients_per_prime=limit_per_p,
                counts=dict(counts),by_prime=rows,exceptions=exceptions,
                direct_negative_checks=negative_checks,first_witness=first_witness(),
                source_sha256={path.name:hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in [Path(__file__),Path(__file__).with_name('elliptic_decoder_probe.py')]})
    Path(__file__).with_name('elliptic_ratio_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--maxp',type=int,default=43)
    ap.add_argument('--limit',type=int,default=0)
    args=ap.parse_args();result=run(args.maxp,args.limit)
    print(json.dumps({'counts':result['counts'],'first_witness':result['first_witness']},indent=2,sort_keys=True))
