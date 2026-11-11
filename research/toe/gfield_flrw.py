"""TOE-04: vacuum, spatially-flat FLRW reduction of Bianconi's Lambda-GfE.

The curvature-only G-field eigenvalue constraint is eliminated *after*
variation of the auxiliary volume multiplier. A source-faithful full theory
with matter needs the dressed matter Euler-Lagrange equations, which are NOT
implemented here. All numerical examples are synthetic dimensionless vacuum
branches, not fitted cosmological predictions.

Sources: arXiv:2610.34496, eqs. (5), (16), (19), (31), (45)-(49);
arXiv:2510.22545, sec III.1, eigenvalues / degeneracies;
Pereira, Phys Rev D 114, 104029 (2026), quadratic-curvature check.
"""
from __future__ import annotations

import math
from fractions import Fraction

# Flattened 0-, 1-, 2-form sectors: eigenvalue u=beta*(ca*A+cb*B),
# where A=Hdot+H**2 and B=H**2+k/a**2.  Isotropic degeneracies sum to 11.
SECTORS = (
    ("scalar", 6, 6, 1),
    ("timelike_vector", 3, 0, 1),
    ("spacelike_vector", 1, 2, 3),
    ("timelike_bivector", 2, 0, 3),
    ("spacelike_bivector", 0, 2, 3),
)


class DomainError(ValueError):
    """The positive induced-metric / expanding-branch domain was exited."""


def _positive_number(x, name):
    if isinstance(x, bool) or not isinstance(x, (int, float, Fraction)):
        raise ValueError(f"{name} must be an explicit number")
    x = float(x)
    if not math.isfinite(x) or x <= 0:
        raise ValueError(f"{name} must be finite and strictly positive")
    return x


def _finite(x, name):
    if isinstance(x, bool) or not isinstance(x, (int, float, Fraction)) or not math.isfinite(x):
        raise ValueError(f"{name} must be finite")
    return float(x)


def curvature_scalars(H, Hdot, *, k_over_a2=0):
    H = _finite(H, "H")
    Hdot = _finite(Hdot, "Hdot")
    return H * H + Hdot, H * H + _finite(k_over_a2, "k/a^2")


def eigenvalues(A, B, beta, *, matter_time=0, matter_space=0):
    """Return (name, multiplicity, u, G) with u<1 and G=(1-u)^-1.

    matter_time/space are alpha*M^time_time / alpha*M^space_space.
    This only evaluates the algebraic isotropic G-field equation and DOES
    NOT provide dynamics for the fluid.
    """
    beta = _positive_number(beta, "beta")
    A, B = _finite(A, "A"), _finite(B, "B")
    tm, sp = _finite(matter_time, "matter_time"), _finite(matter_space, "matter_space")
    shifts = (0.0, tm, sp, 0.0, 0.0)
    result = []
    for (name, ca, cb, mult), matter in zip(SECTORS, shifts):
        u = beta * (ca * A + cb * B) - matter
        denom = 1.0 - u
        if not math.isfinite(u) or denom <= 0:
            raise DomainError(f"positive G-field domain lost in {name}: 1-u={denom}")
        result.append((name, mult, u, 1.0 / denom))
    return tuple(result)


def fluid_eigenvalues(A, B, beta, alpha_rho, w):
    """Algebraic fluid-sector diagnostic, following arXiv:2510.22545 eq49.

    d=4 and U^mu U_mu=-1. The mixed fluid blocks are
    alpha M^0_0=-alpha*rho*(3+5w)/8 and
    alpha M^i_i= alpha*rho*(1-w)/8, with M_0=M_2=0.
    Conservation and metric variation of a fluid remain unimplemented.
    """
    ar, w = _finite(alpha_rho, "alpha_rho"), _finite(w, "w")
    return eigenvalues(A, B, beta,
                       matter_time=-ar * (3+5*w) / 8,
                       matter_space=ar * (1-w) / 8)


def invariant(A, B, beta):
    """Geometric action f, its partials f_A/f_B and Hessian entries.

    f=-sum multiplicity*log(1-u_i). Lambda is excluded here and added
    only after using the off-shell volume constraint to vary the action.
    """
    eig = eigenvalues(A, B, beta)
    beta = float(beta)
    f = fa = fb = faa = fab = fbb = 0.0
    for (name, ca, cb, mult), (_, _, u, G) in zip(SECTORS, eig):
        d = 1.0 - u
        f -= mult * math.log1p(-u)
        fa += mult * beta * ca / d
        fb += mult * beta * cb / d
        faa += mult * beta**2 * ca**2 / d**2
        fab += mult * beta**2 * ca * cb / d**2
        fbb += mult * beta**2 * cb**2 / d**2
    return (f, fa, fb, faa, fab, fbb)


def hessian_direction(A, B, beta, x, y):
    """Positive quadratic form for every nonzero direction (x,y)."""
    x, y = _finite(x, "direction x"), _finite(y, "direction y")
    eig = eigenvalues(A, B, beta)
    return sum(mult * (beta * (ca*x+cb*y) / (1-u))**2
               for (_, ca, cb, mult), (_, _, u, _) in zip(SECTORS, eig))


def lambda_g(A, B, beta):
    """Lambda_G = sum weights (G-1-ln G)/(6 beta), eq. (19)."""
    eig = eigenvalues(A, B, beta)
    return sum(mult * (G - 1.0 + math.log1p(-u))
               for _, mult, u, G in eig) / (6.0 * beta)


def vacuum_lapse_constraint(H, Hdot, Hddot, beta, Lambda):
    """N-variation of S=integral N*a^3 [f(A,B)-6*beta*Lambda].

    With N(t), A=addot/(a N^2)-adot Ndot/(a N^3),
    B=(adot/(a N))^2, then set N=1 AFTER variation:
      f-6bL + (H^2-Hdot)f_A -2H^2 f_B + H*d(f_A)/dt=0.
    """
    H, q, j = _positive_number(H, "H"), _finite(Hdot, "Hdot"), _finite(Hddot, "Hddot")
    A, B = curvature_scalars(H, q)
    f, fa, fb, faa, fab, _ = invariant(A, B, beta)
    fa_dot = faa * (j + 2 * H*q) + fab * (2 * H*q)
    return f - 6*beta*_finite(Lambda, "Lambda") + (H*H-q)*fa - 2*H*H*fb + H*fa_dot


def acceleration(H, Hdot, beta, Lambda):
    """Unique vacuum Hddot on H>0 and beta>0, where f_AA>0."""
    H, q = _positive_number(H, "H"), _finite(Hdot, "Hdot")
    A, B = curvature_scalars(H, q)
    f, fa, fb, faa, fab, _ = invariant(A, B, beta)
    return (6*beta*_finite(Lambda, "Lambda") - f - (H*H-q)*fa
            + 2*H*H*fb - 2*H*H*q*(faa+fab)) / (H*faa)


def de_sitter_lambda(H, beta):
    """Lambda required by the vacuum constraint for constant H>0."""
    H = _positive_number(H, "H")
    f, fa, fb, *_ = invariant(H*H, H*H, beta)
    return (f + H*H*(fa - 2*fb)) / (6 * beta)


def evolve_redshift(redshifts, *, beta, Lambda, H0=1.0, Hdot0=0.0, max_step=0.001):
    """RK4 vacuum branch, z-time equations dH/dz=-Hdot/[(1+z)H].

    Units H_*=1; beta and Lambda are beta*H_*^2, Lambda/H_*^2.
    A numerical solution of the flat *vacuum* reduced action is produced.
    """
    beta = _positive_number(beta, "beta")
    max_step = _positive_number(max_step, "max_step")
    H = _positive_number(H0, "H0")
    Hdot = _finite(Hdot0, "Hdot0")
    zvalues = tuple(_finite(z, "redshift") for z in redshifts)
    if not zvalues or zvalues[0] != 0.0 or any(z < 0 for z in zvalues) or \
            any(a >= b for a,b in zip(zvalues,zvalues[1:])):
        raise ValueError("redshifts must start at zero and increase strictly")
    Lambda = _finite(Lambda, "Lambda")
    def deriv(z, h, q):
        j = acceleration(h,q,beta,Lambda)
        return -q/((1+z)*h), -j/((1+z)*h)
    result = []
    z = 0.0
    for target in zvalues:
        if target > z:
            steps = math.ceil((target-z)/max_step)
            dz = (target-z)/steps
            for _ in range(steps):
                p1,r1 = deriv(z,H,Hdot)
                p2,r2 = deriv(z+dz/2,H+dz*p1/2,Hdot+dz*r1/2)
                p3,r3 = deriv(z+dz/2,H+dz*p2/2,Hdot+dz*r2/2)
                p4,r4 = deriv(z+dz,H+dz*p3,Hdot+dz*r3)
                H += dz*(p1+2*p2+2*p3+p4)/6
                Hdot += dz*(r1+2*r2+2*r3+r4)/6
                z += dz
            z = target
        A,B = curvature_scalars(H,Hdot)
        geig = eigenvalues(A,B,beta)
        j = acceleration(H,Hdot,beta,Lambda)
        result.append({
            "z": float(target), "H": H, "Hdot": Hdot, "Hddot": j,
            "G": tuple(g for _,_,_,g in geig),
            "G_min": min(g for _,_,_,g in geig),
            "lambda_G": lambda_g(A,B,beta),
            "constraint_residual": vacuum_lapse_constraint(H,Hdot,j,beta,Lambda),
        })
    return tuple(result)


def curvature_polynomial(A, B):
    """Exact integer/rational curvature invariants on spatially-flat FLRW.

    Trace U^2/beta^2 = R^2 + Ricci^2 + Riemann^2
                      = 5 Ricci^2 + GaussBonnet,
    where GaussBonnet=24 A B in four dimensions.
    """
    R = 6*(A+B)
    Ricci2 = (3*A)**2 + 3*(A+2*B)**2
    Riemann2 = 12*(A*A+B*B)
    Euler = 24*A*B
    flatten = sum(mult*(ca*A+cb*B)**2 for _,ca,cb,mult in SECTORS)
    return {"R":R, "Ricci2":Ricci2, "Riemann2":Riemann2,
            "GaussBonnet":Euler, "flattened_quad":flatten}


def reference_experiment():
    """High-curvature *synthetic* vacuum trajectory and old TOE-03 covariance."""
    from .bianconi_profile import (frw_design, profile, synthetic_covariance)
    z = tuple(Fraction(i,5) for i in range(7))
    beta, h0, q0 = 0.02, 1.0, -0.01
    Lambda = de_sitter_lambda(h0,beta)
    curve = evolve_redshift(z,beta=beta,Lambda=Lambda,H0=h0,Hdot0=q0)
    e2 = tuple(Fraction(f'{r["H"]**2:.12f}') for r in curve)
    fit = profile(e2, frw_design(z), synthetic_covariance(z))
    return {
        "schema": "mathcan.toe04.v1",
        "source": "arxiv:2610.34496 and arxiv:2510.22545",
        "model": "spatially flat vacuum metric-only ΛGfE, algebraic G constraint",
        "evidence": "synthetic; no matter-coupled or observed H(z)",
        "units": "H*=1; dimensionless beta=beta_phys*H*^2, Lambda=Lambda_phys/H*^2",
        "beta": beta, "Lambda": Lambda, "H0": h0, "Hdot0": q0,
        "redshifts": [str(x) for x in z],
        "H": [round(x["H"],12) for x in curve],
        "G_min": [round(x["G_min"],12) for x in curve],
        "lambda_G": [round(x["lambda_G"],12) for x in curve],
        "max_abs_constraint_residual": max(abs(x["constraint_residual"]) for x in curve),
        "profiled_synthetic_chi2": float(fit["chi2"]),
        "profiled_synthetic_snr": math.sqrt(float(fit["chi2"])),
        "covariance_source": "TOE-03 synthetic covariance, 7 redshifts z=0..6/5",
    }

if __name__ == "__main__":
    import json
    print(json.dumps(reference_experiment(), indent=2, sort_keys=True))
