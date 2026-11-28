"""DEL-03: exact rational pole certificates for algebraic part of Lemma 2.

A finite arithmetic model, not a complex-analytic radius theorem.
The general complex power-series and k->infinity arguments remain external.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import prod

def spectrum(entries, allow_virtual=False):
    acc={}
    for raw_lam,raw_mult in entries:
        lam,m=Q(raw_lam),int(raw_mult)
        if not lam: raise ValueError("automorphism eigenvalues must be nonzero")
        if not allow_virtual and m<1:
            raise ValueError("genuine multiplicity must be positive")
        acc[lam]=acc.get(lam,0)+m
    return tuple(sorted((lam,m) for lam,m in acc.items() if m))

def power_trace(entries,n,allow_virtual=False):
    if n<1: raise ValueError("n must be positive")
    return sum((Q(m)*lam**n for lam,m in spectrum(entries,allow_virtual)),Q(0))

def hankel(entries,size=None,allow_virtual=False):
    sp=spectrum(entries,allow_virtual)
    s=len(sp) if size is None else size
    return tuple(tuple(power_trace(sp,i+j+1,True)
                       for j in range(s)) for i in range(s))

def determinant(matrix):
    n=len(matrix)
    if any(len(row)!=n for row in matrix): raise ValueError("square matrix")
    a=[list(map(Q,row)) for row in matrix]
    det=Q(1)
    for i in range(n):
        k=next((j for j in range(i,n) if a[j][i]),None)
        if k is None: return Q(0)
        if k!=i:
            a[i],a[k]=a[k],a[i]
            det=-det
        pivot=a[i][i]
        det*=pivot
        for j in range(i+1,n):
            factor=a[j][i]/pivot
            for z in range(i+1,n):
                a[j][z]-=factor*a[i][z]
            a[j][i]=Q(0)
    return det

def vandermonde_det_squared(entries,allow_virtual=False):
    sp=spectrum(entries,allow_virtual)
    return prod((Q(m)*lam for lam,m in sp),start=Q(1))*prod(
        ((b[0]-a[0])**2 for a,b in combinations(sp,2)),start=Q(1))

def polynomial_from_roots(entries,allow_virtual=False):
    coeff=[Q(1)]
    for lam,_ in spectrum(entries,allow_virtual):
        nextc=[Q(0)]*(len(coeff)+1)
        for i,c in enumerate(coeff):
            nextc[i]-=lam*c
            nextc[i+1]+=c
        coeff=nextc
    return tuple(coeff)

def solve(a,b):
    n=len(b)
    if len(a)!=n or any(len(row)!=n for row in a):
        raise ValueError("shape")
    mat=[list(map(Q,row))+[Q(rhs)] for row,rhs in zip(a,b)]
    for i in range(n):
        k=next((j for j in range(i,n) if mat[j][i]),None)
        if k is None: raise ValueError("Hankel matrix singular")
        mat[i],mat[k]=mat[k],mat[i]
        pivot=mat[i][i]
        mat[i]=[v/pivot for v in mat[i]]
        for j in range(n):
            if j==i: continue
            factor=mat[j][i]
            mat[j]=[x-factor*y for x,y in zip(mat[j],mat[i])]
    return tuple(row[-1] for row in mat)

def recover_monic_recurrence(entries,allow_virtual=False):
    sp=spectrum(entries,allow_virtual)
    s=len(sp)
    H=hankel(sp,s,True)
    rhs=tuple(-power_trace(sp,s+i+1,True) for i in range(s))
    return solve(H,rhs)+(Q(1),)

def pole_coefficient(entries,eigenvalue,allow_virtual=False):
    """The exact value of (1-lambda*z)G(z) at z=1/lambda."""
    return Q(dict(spectrum(entries,allow_virtual)).get(Q(eigenvalue),0))

def certificate(entries):
    sp=spectrum(entries)
    H=hankel(sp)
    det=determinant(H)
    expected=vandermonde_det_squared(sp)
    poly=polynomial_from_roots(sp)
    recovered=recover_monic_recurrence(sp)
    if det!=expected or det==0 or recovered!=poly:
        raise AssertionError("exact certificate failed")
    if any(pole_coefficient(sp,lam)!=m for lam,m in sp):
        raise AssertionError("lost pole")
    for n in range(1,len(sp)+4):
        if sum((poly[j]*power_trace(sp,n+j)
                for j in range(len(sp)+1)),Q(0)):
            raise AssertionError("recurrence failed")
    return {"distinct_eigenvalues":len(sp),"Hankel_det":str(det),
            "monic_coefficients":[str(c) for c in poly],
            "pole_multiplicities":[m for lam,m in sp]}
