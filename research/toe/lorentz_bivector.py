"""TOE-09. Exact Lorentzian 2-form operator for a DECLARED gauge-field extension.

Bianconi, Gravity from Entropy (2025), Appendix A introduces F⊗F for an
Abelian gauge field; Appendix B defines the bivector operator by raising the
second bivector pair with g_(2). We examine the *assumed* sum over two
colour-isotropic triples, not a derivation of non-Abelian GfE field equations.

Spacetime signature (-,+,+,+), orthonormal ordered bivector basis
(01,02,03,23,31,12), 2-form metric S=diag(-1,-1,-1,+1,+1,+1).
All values are exact Fraction. No complex floats, parameter tuning, or ODE fit.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Sequence


def q(x):
    if type(x) is bool:
        raise ValueError('booleans are not amplitudes')
    return F(x)


def _pair(x):
    if len(x) != 2:
        raise ValueError('exactly two triplet flavors required')
    return tuple(map(q, x))


def coefficients(electric: Sequence, magnetic: Sequence):
    """Euclidean covariant Gram coefficients e,b,c in an orthonormal frame."""
    x, y = _pair(electric), _pair(magnetic)
    e = x[0]**2 + x[1]**2
    b = y[0]**2 + y[1]**2
    c = x[0]*y[0] + x[1]*y[1]
    w = x[0]*y[1] - x[1]*y[0]
    assert e*b - c*c == w*w
    return e, b, c, w


def rotate_flavors(electric, magnetic, rotation):
    """Apply a common rational O(2) flavor-basis change to both 2-vectors.

    This is a *flavor-frame* symmetry, not the non-Abelian gauge symmetry.
    """
    E,B=_pair(electric),_pair(magnetic)
    if len(rotation)!=2 or any(len(row)!=2 for row in rotation):
        raise ValueError('2×2 O(2) matrix required')
    r=tuple(tuple(map(q,row)) for row in rotation)
    if (r[0][0]*r[0][0]+r[1][0]*r[1][0]!=1 or
        r[0][1]*r[0][1]+r[1][1]*r[1][1]!=1 or
        r[0][0]*r[0][1]+r[1][0]*r[1][1]!=0):
        raise ValueError('orthogonal rotation required')
    return (tuple(sum((r[i][j]*E[j] for j in range(2)),F(0)) for i in range(2)),
            tuple(sum((r[i][j]*B[j] for j in range(2)),F(0)) for i in range(2)))


def covariant_gram6(electric, magnetic):
    e, b, c, _ = coefficients(electric, magnetic)
    return tuple(tuple((e if i==j and i<3 else
                        b if i==j and i>=3 else
                        c if (i+3==j or j+3==i) else F(0))
                       for j in range(6)) for i in range(6))


def raised_gram6(electric, magnetic):
    """Covariant Gram times Lorentz bivector metric on its second index."""
    G = covariant_gram6(electric, magnetic)
    signature = (-1,-1,-1,1,1,1)
    return tuple(tuple(G[i][j]*signature[j] for j in range(6)) for i in range(6))


def exact_determinant(matrix):
    """Exact rational determinant, using Gaussian elimination and row parity."""
    rows = [list(map(q,r)) for r in matrix]
    n = len(rows)
    if n == 0 or any(len(r) != n for r in rows):
        raise ValueError('nonempty square matrix required')
    det = F(1)
    for i in range(n):
        pivot = next((j for j in range(i,n) if rows[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            rows[i], rows[pivot] = rows[pivot], rows[i]
            det = -det
        v = rows[i][i]
        det *= v
        for j in range(i+1,n):
            factor = rows[j][i]/v
            if factor:
                for k in range(i+1,n):
                    rows[j][k] -= factor*rows[i][k]
                rows[j][i] = F(0)
    return det


@dataclass(frozen=True)
class LorentzBlock:
    electric: F
    magnetic: F
    mixed: F
    theta_e: F
    theta_b: F
    offdiag: F
    gap: F
    trace: F
    determinant: F
    discriminant: F
    exact_positive_real: bool
    diagonalizable: bool


def source_block(electric, magnetic, *, alpha, beta, H, Hdot, curvature=0):
    """One of three identical 2×2 blocks of Theta=I+alpha M-beta R.

    M=([[ -e, c ],[ -c, b ]]) is induced by F_cov⊗F_cov and the
    Lorentzian bivector metric. R has E=2(H²+Hdot), B=2(H²+curvature).
    A non-Abelian colour sum and the coupling to full GfE are assumptions.
    """
    alpha, beta, H, Hdot, curvature = map(q,(alpha,beta,H,Hdot,curvature))
    if alpha <= 0 or beta <= 0:
        raise ValueError('positive couplings required')
    e,b,c,_ = coefficients(electric,magnetic)
    dE = 1-alpha*e-2*beta*(H*H+Hdot)
    dB = 1+alpha*b-2*beta*(H*H+curvature)
    off = alpha*c
    gap = dE-dB
    trace = dE+dB
    det = dE*dB+off*off
    disc = gap*gap-4*off*off
    diagonalizable = disc != 0 or off == 0
    # Positive real, semisimple generalized eigenvalue spectrum.
    safe = disc >= 0 and diagonalizable and trace > 0 and det > 0
    assert disc == trace*trace-4*det
    return LorentzBlock(e,b,c,dE,dB,off,gap,trace,det,disc,safe,diagonalizable)


def critical_perturbation(u,v,t,alpha):
    """Exact discriminant near a diagonal-matched baseline.

    E=(u,-u+t), B=(v,v). Curvature gap is frozen at its matched t=0
    value: 2 beta (A-B)=-2 alpha (u²+v²). Then
    D=alpha² t² [(2u-t)²-4v²].
    """
    u,v,t,alpha=map(q,(u,v,t,alpha))
    return alpha*alpha*t*t*((2*u-t)**2-4*v*v)


def root_interval_from_trace(block):
    """Exact root sign if sqrt-discriminant is rational, else discriminant only."""
    if block.discriminant < 0:
        return 'complex_pair'
    if block.discriminant == 0 and not block.diagonalizable:
        return 'defective_repeated'
    if block.exact_positive_real:
        return 'positive_real'
    return 'real_nonpositive_or_mixed'


def reference_example():
    alpha,beta = F(1,10), F(1,50)
    H,Hdot=F(1),F(-1,100)
    u,v,t=F(1,50), F(1,25), F(1,1000)
    baseline=source_block((u,-u),(v,v),alpha=alpha,beta=beta,H=H,Hdot=Hdot)
    perturbed=source_block((u,-u+t),(v,v),alpha=alpha,beta=beta,H=H,Hdot=Hdot)
    assert baseline.gap==baseline.mixed==0
    assert baseline.exact_positive_real
    assert perturbed.discriminant==critical_perturbation(u,v,t,alpha)<0
    return {
        'source':'Bianconi 2025 Appendix A gauge F⊗F plus Appendix B bivector metric',
        'extension':'declared two-flavour colour-isotropic sum, not source-derived SU(2) GfE action',
        'alpha':str(alpha),'beta':str(beta),'H':str(H),'Hdot':str(Hdot),
        'E0':list(map(str,(u,-u))), 'B0':list(map(str,(v,v))),
        'E_perturbed':list(map(str,(u,-u+t))),
        'baseline_theta':str(baseline.theta_e),
        'baseline_positive_real':baseline.exact_positive_real,
        'perturbed_discriminant':str(perturbed.discriminant),
        'perturbed_eigenvalue_status':root_interval_from_trace(perturbed),
        'covariant_gram_determinant':str(exact_determinant(covariant_gram6((u,-u),(v,v)))),
        'raised_gram_determinant':str(exact_determinant(raised_gram6((u,-u),(v,v)))),
    }


if __name__=='__main__':
    import json
    print(json.dumps(reference_example(),indent=2,sort_keys=True))
