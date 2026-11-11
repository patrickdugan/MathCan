"""TOE-04: flat vacuum ΛGfE FLRW sector, with algebraic G-field elimination.

The 5 eigenvalue sectors follow Bianconi, arXiv:2510.22545 III.1,
and ΛGfE, arXiv:2610.34496 eqs. (5), (16), (19), (31), (45)-(49).
This solves the *vacuum* lapse-reduced action. A coupled dressed-fluid
Euler-Lagrange model and observational H(z) are NOT supplied.
"""
from __future__ import annotations
import math
from fractions import Fraction

SECTORS = (
    ("scalar", 6, 6, 1),
    ("timelike_vector", 3, 0, 1),
    ("spacelike_vector", 1, 2, 3),
    ("timelike_bivector", 2, 0, 3),
    ("spacelike_bivector", 0, 2, 3),
)

class DomainError(ValueError):
    """Nonpositive induced-metric eigenvalue or invalid expanding branch."""

def _finite(v, name):
    if isinstance(v, bool) or not isinstance(v, (int, float, Fraction)) or not math.isfinite(v):
        raise ValueError(f"{name} must be finite")
    return float(v)

def _positive(v, name):
    v = _finite(v, name)
    if v <= 0:
        raise ValueError(f"{name} must be positive")
    return v

def curvature_scalars(H, Hdot, *, k_over_a2=0):
    H, Hdot = _finite(H,"H"), _finite(Hdot,"Hdot")
    return H*H + Hdot, H*H + _finite(k_over_a2,"k/a^2")

def eigenvalues(A,B,beta, *, matter_time=0,matter_space=0):
    """(sector, degeneracy, u_k, G_k), with G_k=(1-u_k)^(-1).

    The optional matter arguments are algebraic alpha*M mixed eigenvalues.
    They provide no closed matter evolution equations.
    """
    beta = _positive(beta,"beta")
    A,B = _finite(A,"A"), _finite(B,"B")
    tm,sp = _finite(matter_time,"matter_time"),_finite(matter_space,"matter_space")
    result = []
    for (name,ca,cb,mult),matter in zip(SECTORS,(0,tm,sp,0,0)):
        u = beta*(ca*A+cb*B)-matter
        if not math.isfinite(u) or 1-u <= 0:
            raise DomainError(f"positive G-field domain lost in {name}")
        result.append((name,mult,u,1/(1-u)))
    return tuple(result)

def fluid_eigenvalues(A,B,beta,alpha_rho,w):
    """Source algebraic fluid blocks, d=4, eq. (49), not a fluid solution."""
    ar,w = _finite(alpha_rho,"alpha_rho"),_finite(w,"w")
    return eigenvalues(A,B,beta,
                       matter_time=-ar*(3+5*w)/8,
                       matter_space=ar*(1-w)/8)

def invariant(A,B,beta):
    """Geometric logarithmic f and derivatives f_A, f_B, f_AA, f_AB, f_BB."""
    eig=eigenvalues(A,B,beta)
    beta=float(beta)
    f=fa=fb=faa=fab=fbb=0.0
    for (_,ca,cb,mult),(_,_,u,_) in zip(SECTORS,eig):
        den=1-u
        f-=mult*math.log1p(-u)
        fa+=mult*beta*ca/den
        fb+=mult*beta*cb/den
        faa+=mult*beta**2*ca**2/den**2
        fab+=mult*beta**2*ca*cb/den**2
        fbb+=mult*beta**2*cb**2/den**2
    return f,fa,fb,faa,fab,fbb

def hessian_direction(A,B,beta,x,y):
    """Strictly positive for nonzero (x,y) inside G positivity domain."""
    x,y=_finite(x,"x"),_finite(y,"y")
    eig=eigenvalues(A,B,beta)
    return sum(mult*(beta*(ca*x+cb*y)/(1-u))**2
               for (_,ca,cb,mult),(_,_,u,_) in zip(SECTORS,eig))

def lambda_g(A,B,beta):
    """Emergent Λ_G=sum z_k (G_k-1-ln G_k)/(6 beta)."""
    eig=eigenvalues(A,B,beta)
    return sum(mult*(G-1+math.log1p(-u))
               for _,mult,u,G in eig)/(6*beta)

def vacuum_lapse_constraint(H,Hdot,Hddot,beta,Lambda):
    """Lapse variation, with N fixed to 1 only after the variation.

    The effective metric first variation of the auxiliary-volume term
    supplies -6 beta Lambda even though its on-shell integrand vanishes.
    """
    H=_positive(H,"H")
    q,j=_finite(Hdot,"Hdot"),_finite(Hddot,"Hddot")
    A,B=curvature_scalars(H,q)
    f,fa,fb,faa,fab,_=invariant(A,B,beta)
    return (f-6*beta*_finite(Lambda,"Lambda")+(H*H-q)*fa
            -2*H*H*fb+H*(faa*(j+2*H*q)+fab*(2*H*q)))

def acceleration(H,Hdot,beta,Lambda):
    """Solve the affine lapse constraint uniquely for Hddot on H>0."""
    H=_positive(H,"H")
    q=_finite(Hdot,"Hdot")
    A,B=curvature_scalars(H,q)
    f,fa,fb,faa,fab,_=invariant(A,B,beta)
    return (6*beta*_finite(Lambda,"Lambda")-f-(H*H-q)*fa
            +2*H*H*fb-2*H*H*q*(faa+fab))/(H*faa)

def de_sitter_lambda(H,beta):
    """Constant Lambda yielding a vacuum de Sitter solution of H=const."""
    H=_positive(H,"H")
    f,fa,fb,*_=invariant(H*H,H*H,beta)
    return (f+H*H*(fa-2*fb))/(6*beta)

def de_sitter_lambda_by_weyl_trace(H,beta):
    """Independent constant-G covariant Weyl trace: Λ=R_G/12-Λ_G.

    Equation (45) of arXiv:2610.34496 with D=0 and T=0 on de Sitter.
    Checks the reduced lapse normalization only for Hdot=Hddot=0.
    """
    H=_positive(H,"H")
    A=B=H*H
    spec=eigenvalues(A,B,beta)
    rg=sum(mult*(ca*A+cb*B)*G
           for (_,ca,cb,mult),(_,_,_,G) in zip(SECTORS,spec))
    return rg/12-lambda_g(A,B,beta)


def evolve_redshift(redshifts, *, beta,Lambda,H0=1.0,Hdot0=0.0,max_step=.001):
    """RK4 in redshift for flat vacuum H and Hdot; enforce positive G field."""
    beta=_positive(beta,"beta")
    max_step=_positive(max_step,"max_step")
    H=_positive(H0,"H0")
    q=_finite(Hdot0,"Hdot0")
    redshifts=tuple(_finite(z,"z") for z in redshifts)
    if (not redshifts or redshifts[0]!=0 or any(z<0 for z in redshifts)
        or any(a>=b for a,b in zip(redshifts,redshifts[1:]))):
        raise ValueError("redshifts must start at zero and strictly increase")
    Lambda=_finite(Lambda,"Lambda")
    z=0.0
    result=[]
    def rhs(z,h,q):
        j=acceleration(h,q,beta,Lambda)
        return -q/((1+z)*h),-j/((1+z)*h)
    for target in redshifts:
        if target>z:
            count=math.ceil((target-z)/max_step)
            step=(target-z)/count
            for _ in range(count):
                x1,y1=rhs(z,H,q)
                x2,y2=rhs(z+step/2,H+x1*step/2,q+y1*step/2)
                x3,y3=rhs(z+step/2,H+x2*step/2,q+y2*step/2)
                x4,y4=rhs(z+step,H+x3*step,q+y3*step)
                H+=step*(x1+2*x2+2*x3+x4)/6
                q+=step*(y1+2*y2+2*y3+y4)/6
                z+=step
            z=target
        A,B=curvature_scalars(H,q)
        g=eigenvalues(A,B,beta)
        j=acceleration(H,q,beta,Lambda)
        result.append({"z":float(z),"H":H,"Hdot":q,"Hddot":j,
                       "G":tuple(v for _,_,_,v in g),
                       "G_min":min(v for _,_,_,v in g),
                       "lambda_G":lambda_g(A,B,beta),
                       "constraint_residual":vacuum_lapse_constraint(H,q,j,beta,Lambda)})
    return tuple(result)

def curvature_polynomial(A,B):
    """Four-dimensional FLRW: Tr Rsector^2 = 5 Ricci^2 + Gauss-Bonnet."""
    R=6*(A+B)
    ricci2=(3*A)**2+3*(A+2*B)**2
    riemann2=12*(A*A+B*B)
    gb=24*A*B
    flattened=sum(mult*(ca*A+cb*B)**2 for _,ca,cb,mult in SECTORS)
    return {"R":R,"Ricci2":ricci2,"Riemann2":riemann2,
            "GaussBonnet":gb,"flattened_quad":flattened}

def reference_experiment():
    """Synthetic vacuum trajectory, profiled using TOE-03 synthetic covariance."""
    from .bianconi_profile import frw_design,profile,synthetic_covariance
    from fractions import Fraction as F
    z=tuple(F(i,5) for i in range(7))
    beta,H0,q0=.02,1.,-.01
    Lambda=de_sitter_lambda(H0,beta)
    curve=evolve_redshift(z,beta=beta,Lambda=Lambda,H0=H0,Hdot0=q0)
    y=tuple(F(f'{r["H"]**2:.12f}') for r in curve)
    fit=profile(y,frw_design(z),synthetic_covariance(z))
    return {
        "schema":"mathcan.toe04.v1",
        "source":"arxiv:2610.34496 and arxiv:2510.22545",
        "model":"spatially flat vacuum metric-only ΛGfE, algebraic G constraint",
        "evidence":"synthetic; no matter-coupled or observed H(z)",
        "units":"H*=1; beta=beta_phys*H*^2, Lambda=Lambda_phys/H*^2",
        "beta":beta,"Lambda":Lambda,"H0":H0,"Hdot0":q0,
        "redshifts":[str(t) for t in z],
        "H":[round(t["H"],12) for t in curve],
        "G_min":[round(t["G_min"],12) for t in curve],
        "lambda_G":[round(t["lambda_G"],12) for t in curve],
        "max_abs_constraint_residual":max(abs(t["constraint_residual"]) for t in curve),
        "profiled_synthetic_chi2":float(fit["chi2"]),
        "profiled_synthetic_snr":math.sqrt(float(fit["chi2"])),
        "covariance_source":"TOE-03 synthetic covariance, z=0..6/5",
    }

if __name__=="__main__":
    import json
    print(json.dumps(reference_experiment(),sort_keys=True,indent=2))
