"""TOE-06: covariant-gate observables for Bianconi's homogeneous scalar GfE.

This is an independent geometry and strict-principal TT audit of TOE-05's
symmetry-reduced trajectory. It does NOT evaluate Bianconi's full dressed
stress tensor or derivative tensor. Those are exposed as mandatory independent
inputs in `covariant_equation_residuals` to avoid false verification.

The strict-principal TT polynomial follows the stated assumptions of
D.S. Pereira, arXiv:2609.03082 (2026). Extending this GfE gate to the
constant-volume Lambda-GfE action assumes its multiplier does not modify the
highest-derivative tensor symbol. The scalar has no two-form background.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import cmath
import math
from typing import Any

from .gfield_scalar_flrw import ScalarModel, reference_experiment

# Eigen-directions of beta times the direct-sum curvature operator on
# scalar, time vector, space vector, E two-form, B two-form components.
MULTIPLICITIES = (1, 1, 3, 3, 3)
CURV_A = (6, 3, 1, 2, 0)
CURV_B = (6, 0, 2, 0, 2)


def _r(x: Any) -> F:
    if isinstance(x, bool):
        raise ValueError("boolean is not a number")
    result = F(x)
    if result.denominator <= 0:
        raise ValueError("invalid rational")
    return result


def flrw_ricci(H, Hdot, curvature=0):
    """Exact FLRW Ricci components in orthonormal time/space frame.

    curvature is K/a^2, q is Hdot; A=H^2+q and B=H^2+K/a^2.
    Trace-free Ricci-squared is 3*(q-K/a^2)^2. Uses (-+++) signature.
    """
    H, q, cur = map(_r, (H, Hdot, curvature))
    A, B = H*H+q, H*H+cur
    R00, Rs, R = -3*A, A+2*B, 6*(A+B)
    tf00 = R00 + R/F(4)
    tfs = Rs - R/F(4)
    inv = tf00*tf00 + 3*tfs*tfs
    assert inv == 3*(q-cur)**2
    return {"A":A,"B":B,"R00":R00,"Rs":Rs,"R":R,
            "TF00":tf00,"TFs":tfs,"tracefree_Ricci_sq":inv,
            "Einstein_locus":q==cur}


def responses(beta, H, Hdot, phi=0, phidot=0, alpha=0, mass=0, curvature=0):
    """Exact G-field spectral inverse response with a homogeneous real scalar.

    In the TT sectors W_E=1/(1-2 beta A), W_B=1/(1-2 beta B),
    W_s=1/(1-beta(A+2B)). The scalar/time-vector sectors carry matter;
    a real homogeneous scalar adds no tensor/bivector background response.
    """
    beta,H,Hdot,phi,phidot,alpha,mass,curvature=map(_r,
        (beta,H,Hdot,phi,phidot,alpha,mass,curvature))
    if beta<=0 or alpha<0 or mass<0:
        raise ValueError("nonnegative scalar coupling, positive curvature coupling")
    A=H*H+Hdot;B=H*H+curvature
    theta=(1+alpha*mass**2*phi**2-6*beta*(A+B),
           1-alpha*phidot**2-3*beta*A,
           1-beta*(A+2*B),
           1-2*beta*A,
           1-2*beta*B)
    if min(theta)<=0:
        raise ValueError("nonpositive induced-metric eigenvalue")
    G=tuple(1/d for d in theta)
    assert G[3]-G[4] == 2*beta*(Hdot-curvature)*G[3]*G[4]
    return {"theta":theta,"G":G,"Ws":G[2],"WE":G[3],"WB":G[4],
            "gap":G[3]-G[4],"A":A,"B":B,"beta":beta,
            "curvature_diff":Hdot-curvature}


def tt_symbol(Ws, WE, WB):
    """Strict-principal transverse-traceless q4(omega,p)/p^4 = a*x^2+b*x+c.

    x=(omega/p)^2. Formula is the two-square principal symbol
    (Ws^2/2)(omega^2-p^2)^2+2(WE omega^2-WB p^2)^2.
    """
    Ws, WE, WB=map(_r,(Ws,WE,WB))
    if min(Ws, WE, WB)<=0:
        raise ValueError("TT eigenvalues must be positive")
    a=Ws**2/F(2)+2*WE**2
    b=-(Ws**2+4*WE*WB)
    c=Ws**2/F(2)+2*WB**2
    disc=b*b-4*a*c
    assert disc == -4*Ws**2*(WE-WB)**2
    return {"a":a,"b":b,"c":c,"discriminant":disc,
            "real_characteristic":disc==0}


def tt_symbol_at(symbol, x):
    x=_r(x)
    return symbol["a"]*x*x+symbol["b"]*x+symbol["c"]


def tt_frequency_ratio(symbol):
    """Principal omega/|p| complex roots; a high-frequency diagnostic only."""
    a,b,disc=map(float,(symbol["a"],symbol["b"],symbol["discriminant"]))
    root=complex(-b,math.sqrt(max(0,-disc)))/(2*a)
    w=cmath.sqrt(root)
    return {"omega_over_p":w,"imag_abs":abs(w.imag),
            "squared_frequency":root}


def tt_gate(beta,H,Hdot,phi=0,phidot=0,alpha=0,mass=0,curvature=0):
    r=responses(beta,H,Hdot,phi,phidot,alpha,mass,curvature)
    t=tt_symbol(r["Ws"],r["WE"],r["WB"])
    ricci=flrw_ricci(H,Hdot,curvature)
    # Δ = -16 β² Ws² WE² WB² (Hdot-K/a²)²
    assert t["discriminant"] == (
        -F(16,3)*r["beta"]**2*r["Ws"]**2*r["WE"]**2*r["WB"]**2
        *ricci["tracefree_Ricci_sq"])
    freq=tt_frequency_ratio(t)
    return {"responses":r,"symbol":t,"Ricci":ricci,"frequency":freq,
            "strict_principal_gate_pass":t["real_characteristic"]}


def gfield_curvature_trace(model:ScalarModel, H,Hdot,phi,phidot):
    """Direct algebraic contraction R_G=sum_i z_i G_i R_i.

    Requires model's independent G-field and scalar-specific tensor terms to
    calculate the rest of the covariant field equations.
    """
    theta=model.spectral(H,Hdot,phi,phidot)
    G=[1/d for d in theta]
    A=H*H+Hdot; B=H*H
    rg=math.fsum(w*g*(x*A+y*B) for w,g,x,y in
                 zip(MULTIPLICITIES,G,CURV_A,CURV_B))
    lg=math.fsum(w*(g-1-math.log(g)) for w,g in zip(MULTIPLICITIES,G))/(6*model.beta)
    # Λ = (RG-D)/12 + κ T/4 - Λ_G
    # => D-3κT = RG-12(Λ+Λ_G).
    required=rg-12*(model.Lambda+lg)
    return {"R_G":rg,"Lambda_G":lg,
            "required_D_minus_3kappaT":required,
            "G_min":min(G)}


@dataclass(frozen=True)
class CovariantComponents:
    """Externally calculated tensors; avoid substituting reduced-action residuals.

    X00 = (R^G_00+D_00), Xs=(R^G_ii+D_ii)/a²,
    rho,p=components of dressed T, R_G its geometric trace,
    D=source's contracted derivative, Lambda_G=emergent term.
    Time derivatives are independent covariant observations.
    """
    X00:float; Xs:float; rho:float; pressure:float
    R_G:float; D:float; Lambda_G:float
    dX00:float; dRG:float; dD:float; dLambdaG:float; drho:float


def covariant_equation_residuals(H, Lambda, kappa, comp:CovariantComponents):
    """Project source Eqs. 45/47/48 to FLRW using supplied tensors.

    These residuals only certify a full solution when all components were
    independently built from the 4D dressed action/G-field geometry.
    """
    if not isinstance(comp,CovariantComponents):
        raise TypeError("full covariant tensor components required")
    vals=(H,Lambda,kappa,*vars(comp).values())
    if any(not math.isfinite(float(x)) for x in vals) or kappa<=0:
        raise ValueError("finite parameters and positive kappa required")
    enthalpy=comp.rho+comp.pressure
    T=-comp.rho+3*comp.pressure
    eq47=comp.X00+comp.Xs-3*kappa*enthalpy
    eq45=12*(Lambda+comp.Lambda_G)-comp.R_G+comp.D-3*kappa*T
    eq48=comp.dX00+3*H*(comp.X00+comp.Xs)+(
        comp.dRG-6*comp.dLambdaG)/2-3*kappa*(comp.drho+3*H*enthalpy)
    return {"trace_free":eq47,"weyl_trace":eq45,"joint_noether":eq48,
            "all_checked":max(abs(eq47),abs(eq45),abs(eq48))<1e-10}


def _partials_time(model,state):
    """First time derivatives of f_A,f_B, from differentiated theta sectors."""
    H,q,phi,pi=state
    p=model.partials(*state)
    _,J,_,P=model.rhs(*state)
    Adot,Bdot=J+2*H*q,2*H*q
    b,a,m2=model.beta,model.alpha,model.mass**2
    d0,d1,d2,d3,d4=p["theta"]
    # f_BB and f_Bphi are independent derivatives of f_B.
    fBB=36*b*b/d0**2+12*b*b/d2**2+12*b*b/d4**2
    fBphi=-12*a*b*m2*phi/d0**2
    fa_dot=p["faa"]*Adot+p["fab"]*Bdot+p["faphi"]*pi+p["fapi"]*P
    fb_dot=p["fab"]*Adot+fBB*Bdot+fBphi*pi
    return fa_dot,fb_dot


def _rk4_time(model,s,h):
    def add(v,k,t):return tuple(x+t*y for x,y in zip(v,k))
    k1=model.rhs(*s)
    k2=model.rhs(*add(s,k1,h/2))
    k3=model.rhs(*add(s,k2,h/2))
    k4=model.rhs(*add(s,k3,h))
    return tuple(x+h*(u+2*v+2*w+z)/6 for x,u,v,w,z in zip(s,k1,k2,k3,k4))


def spatial_minisuperspace_residual(model,state, step=1e-4):
    """Independent a-variation of N=1 reduced action, with f_A double dot.

    The last derivative is a centered finite difference along the coupled ODE.
    This tests symmetry-reduced Euler-Lagrange/Noether closure, NOT full
    R^G_mu nu, D_mu nu or dressed T_mu nu covariant equations.
    """
    H,q,phi,pi=map(float,state)
    if step<=0 or not math.isfinite(step):raise ValueError("positive step required")
    s=(H,q,phi,pi)
    p=model.partials(*s)
    fa_dot,fb_dot=_partials_time(model,s)
    plus=_rk4_time(model,s,step)
    minus=_rk4_time(model,s,-step)
    fa_ddot=(_partials_time(model,plus)[0]-_partials_time(model,minus)[0])/(2*step)
    F=p["f"]-6*model.beta*model.Lambda
    # Euler-Lagrange for a in L=a³[f(A,B,phi,pi)-6βΛ],
    # A=ä/a, B=(ȧ/a)² at N=1.
    residual=(3*F+(3*H*H+q)*p["fa"]-(6*H*H+2*q)*p["fb"]+
              4*H*fa_dot-2*H*fb_dot+fa_ddot)
    return {"spatial_EL":residual,"fa_dot":fa_dot,"fb_dot":fb_dot,
            "fa_ddot":fa_ddot,"step":step}


def reference_audit():
    experiment=reference_experiment()
    model=ScalarModel(experiment["beta"],experiment["alpha"],experiment["mass"],
                      experiment["Lambda"])
    entries=[]
    for rec in experiment["curve"]:
        z,H,q,phi,pi=(rec[k] for k in ("z","H","Hdot","phi","phidot"))
        gate=tt_gate(F(str(model.beta)),F(str(H)),F(str(q)),F(str(phi)),F(str(pi)),
                     F(str(model.alpha)),F(str(model.mass)))
        source=gfield_curvature_trace(model,H,q,phi,pi)
        s=spatial_minisuperspace_residual(model,(H,q,phi,pi))
        entries.append({"z":z,"Hdot":q,
                        "Ricci_TF2":float(gate["Ricci"]["tracefree_Ricci_sq"]),
                        "tt_discriminant":float(gate["symbol"]["discriminant"]),
                        "tt_gate_pass":gate["strict_principal_gate_pass"],
                        "Im_omega_over_p":gate["frequency"]["imag_abs"],
                        "R_G":source["R_G"],"Lambda_G":source["Lambda_G"],
                        "required_D_minus_3kappaT":source["required_D_minus_3kappaT"],
                        "spatial_reduced_EL":s["spatial_EL"]})
    return {"schema":"mathcan.toe06.covariant_gates.v1",
            "source_pins":{"Bianconi":"arxiv:2610.34496",
                           "Pereira":"arxiv:2609.03082",
                           "MathCan_TOE05":"d001d3feb43fb5cf5c15107c55016c0cc77a9524"},
            "data_type":"synthetic symmetry-reduced trajectory",
            "full_covariant_tensor_evidence":False,
            "tt_gate_assumptions":"Pereira single-multiplet symmetry-inheriting strict-principal sector; constant-volume Lambda does not alter four-derivative tensor symbol",
            "entries":entries}

if __name__ == "__main__":
    import json
    print(json.dumps(reference_audit(),indent=2))
