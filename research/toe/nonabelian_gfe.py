"""TOE-10: gauge-covariant SU(2)^2 source and Lorentzian spectral dynamics.

The matter extension M_(2)[I,J] = sum_{flavor,color} F_(I)^a F_(J)^a
is a *proposed* non-Abelian extension of Bianconi's Abelian Appendix-A
operator, not a derivation from the full Dirac--Kaehler / G-field action.

Two independent SU(2) transformations act on adjoint color indices; their
Killing-form contractions are invariant. The cosmological tests use a
spatially flat Einstein--Yang--Mills background. A separately defined
log-determinant gauge-medium Lagrangian supplies a concrete local field
variation on a prescribed FLRW metric, not full Lambda-GfE metric dynamics.

Pure Python Fraction arithmetic. Sign conventions: (-,+,+,+), flattened
bivector (01,02,03,23,31,12), S=diag(-I3,+I3).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence

from .lorentz_bivector import source_block, raised_gram6
from .yang_mills_triads import Triad, einstein_ym_tangent, einstein_ym_lambda


def rat(x):
    if type(x) is bool:
        raise ValueError("boolean is not a physical parameter")
    return Q(x)


IDENTITY = ((Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))


def rotation3(m):
    """Exact SO(3) matrix for a possible adjoint gauge-frame rotation."""
    if len(m) != 3 or any(len(row) != 3 for row in m):
        raise ValueError("SO(3) rotation must be 3x3")
    r = tuple(tuple(map(rat, row)) for row in m)
    for i in range(3):
        for j in range(3):
            if sum((r[k][i]*r[k][j] for k in range(3)), Q(0)) != (1 if i == j else 0):
                raise ValueError("not an orthogonal adjoint rotation")
    det = (r[0][0]*(r[1][1]*r[2][2]-r[1][2]*r[2][1])
           -r[0][1]*(r[1][0]*r[2][2]-r[1][2]*r[2][0])
           +r[0][2]*(r[1][0]*r[2][1]-r[1][1]*r[2][0]))
    if det != 1:
        raise ValueError("SO(3) rotation must preserve orientation")
    return r


def covariant_colour_gram(triads: Sequence[Triad], rotations=None):
    """M_AB=sum_I,a F^a_IA F^a_IB with independent adjoint SO(3) frames.

    In one color frame, the orthonormal bivector components are
    F^a_(0i)=E delta^a_i and F^a_(jk)=B epsilon^a_jk.
    The Killing-form color contraction removes dependence on the gauge frame.
    """
    if not triads:
        raise ValueError("at least one gauge triplet required")
    if rotations is None:
        rotations = (IDENTITY,) * len(triads)
    if len(rotations) != len(triads):
        raise ValueError("one color frame per independent gauge factor")
    matrix = [[Q(0) for _ in range(6)] for _ in range(6)]
    for t, frame in zip(triads, rotations):
        rot = rotation3(frame)
        for adj in range(3):
            f = [t.electric*rot[adj][i] for i in range(3)] + [t.magnetic*rot[adj][i] for i in range(3)]
            for i in range(6):
                for j in range(6):
                    matrix[i][j] += f[i]*f[j]
    return tuple(tuple(row) for row in matrix)


def lorentz_colour_operator(triads: Sequence[Triad], rotations=None):
    m = covariant_colour_gram(triads,rotations)
    return tuple(tuple(m[i][j]*(-1 if j < 3 else 1) for j in range(6)) for i in range(6))


def invariants(triads: Sequence[Triad]):
    if not triads:
        raise ValueError("nonempty multiplet list required")
    e = sum((t.electric*t.electric for t in triads), Q(0))
    b = sum((t.magnetic*t.magnetic for t in triads), Q(0))
    c = sum((t.electric*t.magnetic for t in triads), Q(0))
    return e,b,c


def gr_background(triads: Sequence[Triad], H, kappa):
    H,kappa=rat(H),rat(kappa)
    if kappa <= 0:
        raise ValueError("positive Einstein coupling required")
    e,b,_=invariants(triads)
    s=e+b
    if s <= 0:
        raise ValueError("nontrivial gauge field required")
    hdot=-kappa*s
    lam=einstein_ym_lambda(triads,H,kappa)
    return hdot,lam


def normalized_mixed_flow(triads: Sequence[Triad], H):
    """Exact Yang--Mills identities sdot=-4Hs, rdot=torque/s for r=c/s."""
    H=rat(H)
    e,b,c=invariants(triads)
    s=e+b
    if s<=0:
        raise ValueError("positive gauge energy required")
    torque=sum((2*t.coupling*t.psi*(t.electric*t.electric-t.magnetic*t.magnetic)
                for t in triads),Q(0))
    edot=sum((2*t.electric*t.tangent(H)[1] for t in triads),Q(0))
    bdot=sum((2*t.magnetic*t.magnetic_dot(H) for t in triads),Q(0))
    cdot=sum((t.tangent(H)[1]*t.magnetic+t.electric*t.magnetic_dot(H)
              for t in triads),Q(0))
    sdot=edot+bdot
    assert sdot == -4*H*s
    assert cdot == -4*H*c+torque
    rdot=(cdot*s-c*sdot)/(s*s)
    assert rdot==torque/s
    return {'e':e,'b':b,'s':s,'c':c,'sdot':sdot,'cdot':cdot,
            'torque':torque,'r':c/s,'rdot':rdot}


def gr_spectrum(triads: Sequence[Triad], H, kappa, beta, alpha):
    H,kappa,beta,alpha=map(rat,(H,kappa,beta,alpha))
    if beta<=0 or alpha<=0:
        raise ValueError('positive response couplings required')
    hdot,lam=gr_background(triads,H,kappa)
    data=normalized_mixed_flow(triads,H)
    s,c=data['s'],data['c']
    block=source_block([t.electric for t in triads],[t.magnetic for t in triads],
                       H=H,Hdot=hdot,beta=beta,alpha=alpha)
    gap=(2*beta*kappa-alpha)*s
    assert block.gap == gap
    assert block.discriminant == gap*gap-4*alpha*alpha*c*c
    assert block.discriminant == s*s*((alpha-2*beta*kappa)**2-4*alpha*alpha*(c/s)**2)
    delta_dot=2*gap*((2*beta*kappa-alpha)*data['sdot'])-8*alpha*alpha*c*data['cdot']
    return {'Hdot':hdot,'Lambda':lam,'gap':gap,'block':block,
            'delta_dot':delta_dot,**data}


def canonical_gr_spectrum(triads,H,kappa,beta):
    kappa,beta=rat(kappa),rat(beta)
    x=gr_spectrum(triads,H,kappa,beta,6*beta*kappa)
    a=6*beta*kappa
    assert x['gap']==-4*beta*kappa*x['s']
    assert x['block'].discriminant == 16*beta*beta*kappa*kappa*(x['s']**2-9*x['c']**2)
    # A zero discriminant with c != 0 is a defective Krein collision.
    return x


def critical_example(inside_electric=Q(0)):
    """GR+YM exact rational state, starts at or inside the Krein boundary."""
    perturb=rat(inside_electric)
    if perturb<0:
        raise ValueError("nonnegative interior perturbation")
    ts=(Triad(1,2,1),Triad(0,1+perturb,1))
    x=canonical_gr_spectrum(ts,Q(1),Q(1,10),Q(1,100))
    return x,ts


@dataclass(frozen=True)
class Medium:
    """Declared minimal YM + sigma[-3 log det2(Theta)] gauge medium.

    This action is gauge invariant via the internal Killing form and curved
    2-form operator. Its matter equations are derived on a prescribed FLRW
    background; no GfE metric/gravity field equation is solved by this class.
    """
    alpha: Q
    beta: Q
    sigma: Q

    def __post_init__(self):
        for field in ('alpha','beta','sigma'):
            object.__setattr__(self,field,rat(getattr(self,field)))
        if self.alpha<=0 or self.beta<=0 or self.sigma<0:
            raise ValueError('positive alpha and beta, nonnegative medium strength')

    def spectral(self, triads,H,Hdot):
        return source_block([t.electric for t in triads],[t.magnetic for t in triads],
                           H=H,Hdot=Hdot,alpha=self.alpha,beta=self.beta)

    def local(self,triads,H,Hdot,require_spectral=True):
        """Exact momenta, field derivatives and E-Hessian of reduced action.

        L_comoving/a³ = 3/2 sum(E²-B²) - 3 sigma log D.
        Spectral admissibility is independently enforced for the log branch.
        """
        x=self.spectral(triads,H,Hdot)
        if require_spectral and not x.exact_positive_real:
            raise ValueError('induced metric not on positive-real semisimple branch')
        e,b,c=invariants(triads)
        E=[t.electric for t in triads]
        B=[t.magnetic for t in triads]
        a=self.alpha;v=self.beta;z=self.sigma
        D=x.determinant
        if D<=0:
            raise ValueError('singular or negative determinant')
        te,tb=x.theta_e,x.theta_b
        n=len(triads)
        numerator=[tb*E[i]-a*c*B[i] for i in range(n)]
        de=[-2*a*tb*E[j]+2*a*a*c*B[j] for j in range(n)]
        db=[2*a*te*B[j]+2*a*a*c*E[j] for j in range(n)]
        p=[3*E[i]+z*6*a*numerator[i]/D for i in range(n)]
        q=[-3*B[i]-z*6*a*(te*B[i]+a*c*E[i])/D for i in range(n)]
        he=[[3*(i==j)+z*6*a*((tb*(i==j)-a*B[i]*B[j])/D
              -numerator[i]*de[j]/(D*D)) for j in range(n)] for i in range(n)]
        hb=[[z*6*a*((2*a*B[j]*E[i]-a*(E[j]*B[i]+c*(i==j)))/D
              -numerator[i]*db[j]/(D*D)) for j in range(n)] for i in range(n)]
        # H, Hdot enter via A=H²+Hdot and B_curv=H².
        pA=[z*6*a*(2*v*tb*numerator[i]/(D*D)) for i in range(n)]
        pB=[z*6*a*((-2*v*E[i])/D+2*v*te*numerator[i]/(D*D)) for i in range(n)]
        return {'momentum':p,'magnetic_momentum':q,'hessian':he,
                'mixed_hessian':hb,'curvature_A':pA,'curvature_B':pB,
                'block':x}

    def electric_acceleration(self,triads,H,Hdot,Hddot):
        """Solve gauge-invariant Euler equations for dot(E_i), exact rational.

        dot(P_i)+2H P_i-2g_i psi_i Q_i = 0.
        P_i=dL/dE_i, Q_i=dL/dB_i. This is the equation of the *declared*
        gauge medium, using specified H,Hdot,Hddot as external geometry.
        """
        H,Hdot,Hddot=map(rat,(H,Hdot,Hddot))
        if len(triads)!=2:
            raise ValueError('two SU(2) multiplets required by this solver')
        r=self.local(triads,H,Hdot)
        Bdot=[t.magnetic_dot(H) for t in triads]
        Adot=2*H*Hdot+Hddot
        Cdot=2*H*Hdot
        p,q=r['momentum'],r['magnetic_momentum']
        rhs=[-2*H*p[i]+2*t.coupling*t.psi*q[i]
             -sum((r['mixed_hessian'][i][j]*Bdot[j] for j in range(2)),Q(0))
             -r['curvature_A'][i]*Adot-r['curvature_B'][i]*Cdot
             for i,t in enumerate(triads)]
        a,b=r['hessian'][0];c,d=r['hessian'][1]
        det=a*d-b*c
        if det==0:
            raise ValueError('degenerate gauge Legendre map')
        result=((rhs[0]*d-b*rhs[1])/det,(a*rhs[1]-c*rhs[0])/det)
        assert all(sum((r['hessian'][i][j]*result[j] for j in range(2)),Q(0)) == rhs[i] for i in range(2))
        return {'electric_dot':result,'kinetic_det':det,'rhs':rhs,'local':r}


def reference_experiment():
    from .yang_mills_triads import einstein_ym_rk4_one_step
    x,ts=critical_example(Q(1,100000))
    H=Q(1);k=Q(1,10);b=Q(1,100)
    h2,ts2=einstein_ym_rk4_one_step(ts,H,k,Q(1,10000))
    later=canonical_gr_spectrum(ts2,h2,k,b)
    boundary,_=critical_example()
    assert x['block'].exact_positive_real
    assert x['block'].discriminant>0>later['block'].discriminant
    assert boundary['delta_dot']==Q(-54,15625)
    r={
      'schema':'mathcan.toe10.nonabelian.v1',
      'provenance':'Bianconi (2025) Abelian F tensor; proposed SU(2)^2 gauge extension',
      'background':'Einstein-Yang-Mills, not the full Lambda-GfE system',
      'alpha':'3/500','beta':'1/100','kappa':'1/10','H0':'1',
      'Lambda0':str(x['Lambda']),'E1':'2','E2':'100001/100000',
      'psi1':'1','psi2':'0',
      'initial_discriminant':str(x['block'].discriminant),
      'initial_positive_real':x['block'].exact_positive_real,
      'time_step':'1/10000','final_discriminant_sign':-1,
      'boundary_discriminant_derivative':str(boundary['delta_dot']),
      'branch_change':'positive-real semisimple to complex pair on prescribed GR+YM evolution'
    }
    return r


if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
