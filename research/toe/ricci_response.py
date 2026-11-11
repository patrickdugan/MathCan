"""TOE-07: FLRW covariant derivative of a Ricci-response tensor.

Conditional surrogate: for L(g,Ricci,fields), P^(mu nu)=dL/dR_(mu nu),
D_(mu nu)=[Box P_(mu nu)+g_(mu nu) div div P
            -2 nabla_alpha nabla_(mu P_(nu))^alpha]/2.
This is the integration-by-parts derivative of the Ricci variation, with
signature (-+++), FLRW lapse 1, and P^00=-U, P^ij=(V/a^2)delta^ij.
Bianconi's GfE action also depends on 2-form/full Riemann curvature; this
Ricci-only completion is NOT the complete source D_(mu nu) tensor.
"""
from fractions import Fraction as Q
from .multiplet_cone import rat


def geometry(H,hdot):
    H,hdot=rat(H),rat(hdot)
    return hdot+3*H*H


def double_divergence(H,hdot,U,V,Udot,Vdot,Uddot):
    H,hdot,U,V,Udot,Vdot,Uddot=map(rat,(H,hdot,U,V,Udot,Vdot,Uddot))
    return -Uddot-6*H*Udot+3*H*Vdot+3*(hdot+3*H*H)*(V-U)


def ricci_d_components(H,hdot,U,V,Udot,Vdot,Uddot,Vddot):
    """Covariant D_00 and D_ii/a2, exact with supplied response derivatives."""
    H,hdot,U,V,Udot,Vdot,Uddot,Vddot=map(rat,(H,hdot,U,V,Udot,Vdot,Uddot,Vddot))
    S=hdot+3*H*H
    d00=Q(3,2)*((U-V)*S+H*(Udot+Vdot))
    ds=-(U-V)*S/Q(2)-(Uddot+Vddot)/Q(2)-2*H*Udot
    return {'D00':d00,'Ds':ds,'trace':-d00+3*ds}


def independent_operator_components(H,hdot,U,V,Udot,Vdot,Uddot,Vddot):
    """Independent intermediate covariant-derivative contractions.

    Reproduces -1/2 divdiv P +1/2 Box P - divdiv P_mixed
    with FLRW Christoffel symbols and an isotropic two-eigenvalue P.
    """
    H,hdot,U,V,Udot,Vdot,Uddot,Vddot=map(rat,(H,hdot,U,V,Udot,Vdot,Uddot,Vddot))
    S=hdot+3*H*H
    div=double_divergence(H,hdot,U,V,Udot,Vdot,Uddot)
    box00=Uddot+3*H*Udot+6*H*H*(V-U)
    boxs=-Vddot-3*H*Vdot+2*H*H*(V-U)
    k00=Uddot+3*H*(Udot-Vdot)+3*H*H*(V-U)
    ks=(V-U)*(hdot+4*H*H)-H*Udot
    return {'D00':(-div+box00-2*k00)/2,'Ds':(div+boxs-2*ks)/2}


def ricci_lift_from_reduced_derivatives(fA,fB,fAdot,fBdot,fAddot,fBddot):
    """A particular isotropic Ricci lift matching f_A and f_B on FLRW.

    A=Hdot+H²,B=H². It matches the reduced first variation but cannot
    determine the off-FLRW response of full-Riemann 2-form terms.
    """
    fA,fB,fAdot,fBdot,fAddot,fBddot=map(rat,
        (fA,fB,fAdot,fBdot,fAddot,fBddot))
    return ((2*fA-fB)/6,fB/6,(2*fAdot-fBdot)/6,fBdot/6,
            (2*fAddot-fBddot)/6,fBddot/6)
