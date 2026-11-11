"""TOE-08: exact two-SU(2)-triad Yang--Mills matter and an assumed 2-form response.

The Yang--Mills action and equations are concrete. The observer-frame, positive
bivector Gram matrix is a declared constitutive map into a candidate GfE
2-form sector; it has NOT been derived from Bianconi's Dirac--Kaehler action.
No coupled Einstein/GfE field equations, metric variation of the GfE coupling,
or metric--matter principal symbol are claimed here.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product


def rat(x):
    if type(x) is bool:
        raise ValueError("boolean is not a numeric field")
    return Q(x)


@dataclass(frozen=True)
class Triad:
    psi: Q
    electric: Q
    coupling: Q

    def __post_init__(self):
        for name in ("psi", "electric", "coupling"):
            object.__setattr__(self, name, rat(getattr(self, name)))
        if self.coupling <= 0:
            raise ValueError("positive SU(2) gauge coupling required")

    @property
    def magnetic(self):
        return self.coupling * self.psi ** 2

    def tangent(self, hubble):
        """Exact homogeneous YM equations with A_i^a=a*psi*delta_i^a.

        dot(psi)=E-H psi, dot(E)=-2 H E-2 g^2 psi^3.
        """
        h = rat(hubble)
        return (self.electric - h * self.psi,
                -2 * h * self.electric - 2 * self.coupling ** 2 * self.psi ** 3)

    def magnetic_dot(self, hubble):
        return 2 * self.coupling * self.psi * self.tangent(hubble)[0]


def epsilon(i, j, k):
    if len({i, j, k}) != 3:
        return 0
    return 1 if (i, j, k) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1


def stress_tensor(triads):
    """Direct contraction T_mn=sum(F_mr F_n^r-g_mn F^2/4).

    Orthonormal tetrad of (-,+,+,+). Each SU(2) multiplet carries the three
    adjoint field strengths F^a_0i=E delta^a_i, F^a_ij=B epsilon_{aij}.
    """
    eta = [-1, 1, 1, 1]
    tensor = [[Q(0) for _ in range(4)] for _ in range(4)]
    for t in triads:
        for adj in range(3):
            F = [[Q(0) for _ in range(4)] for _ in range(4)]
            for i in range(3):
                F[0][i+1] = t.electric if adj == i else Q(0)
                F[i+1][0] = -F[0][i+1]
                for j in range(3):
                    F[i+1][j+1] = t.magnetic * epsilon(adj,i,j)
            norm = sum((eta[i] * eta[j] * F[i][j] ** 2
                        for i in range(4) for j in range(4)), Q(0))
            for mu in range(4):
                for nu in range(4):
                    v = sum((eta[r] * F[mu][r] * F[nu][r] for r in range(4)), Q(0))
                    if mu == nu:
                        v -= eta[mu] * norm / 4
                    tensor[mu][nu] += v
    return tuple(tuple(row) for row in tensor)


def energy_pressure(triads):
    density = Q(3, 2) * sum((t.electric**2 + t.magnetic**2 for t in triads), Q(0))
    return density, density / 3


def energy_rate(triads, hubble):
    return Q(3) * sum((t.electric*t.tangent(hubble)[1] +
                       t.magnetic*t.magnetic_dot(hubble)
                       for t in triads), Q(0))


def response_blocks(triads):
    if not triads:
        raise ValueError("at least one multiplet is required")
    me = sum((t.electric**2 for t in triads), Q(0))
    mb = sum((t.magnetic**2 for t in triads), Q(0))
    mix = sum((t.electric*t.magnetic for t in triads), Q(0))
    return me, mb, mix


def response_matrix(triads):
    """Positive observer-frame Gram M_AB=sum_(multiplet,adj) F_A F_B.

    Indices 0..2 are electric, 3..5 magnetic (isotropic common frame).
    Constitutive map to GfE is an explicit assumption, not a source result.
    """
    me, mb, mix = response_blocks(triads)
    return tuple(tuple((me if i == j and i < 3 else
                        mb if i == j and i >= 3 else
                        mix if abs(i-j) == 3 else Q(0))
                       for j in range(6)) for i in range(6))


def det_exact(matrix):
    """Independent exact rational determinant by row reduction."""
    a = [[rat(x) for x in row] for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("square matrix required")
    det = Q(1)
    for c in range(n):
        r = next((i for i in range(c, n) if a[i][c]), None)
        if r is None:
            return Q(0)
        if r != c:
            a[c], a[r] = a[r], a[c]
            det = -det
        pivot = a[c][c]
        det *= pivot
        for i in range(c + 1, n):
            f = a[i][c] / pivot
            for j in range(c+1, n):
                a[i][j] -= f*a[c][j]
            a[i][c] = Q(0)
    return det


def gram_det_formula(triads):
    me, mb, mix = response_blocks(triads)
    return (me * mb - mix**2)**3


def two_multiplet_wedge(triads):
    if len(triads) != 2:
        raise ValueError("exact two-multiplet formula")
    a, b = triads
    return a.electric*b.magnetic - b.electric*a.magnetic


def induced_response(triads, H, Hdot, beta, alpha, curvature=0):
    """Declared 6x6 induced metric Theta=I+alpha*M-beta*R, in E/B basis.

    This is the graph/observer-positive constitutive ansatz of TOE-07 extended
    to its essential nonzero electric--magnetic mixing. A true GfE comparison
    must recover the 2-form operator and its Lorentzian sign conventions.
    """
    H, Hdot, beta, alpha, curvature = map(rat, (H,Hdot,beta,alpha,curvature))
    if beta <= 0 or alpha <= 0:
        raise ValueError("positive couplings required")
    me, mb, mix = response_blocks(triads)
    A, B = H*H + Hdot, H*H + curvature
    te = 1 + alpha*me - 2*beta*A
    tb = 1 + alpha*mb - 2*beta*B
    off = alpha*mix
    block_det = te*tb-off*off
    if te <= 0 or block_det <= 0:
        raise ValueError("induced 2-form metric is not positive definite")
    return {"thetaE":te, "thetaB":tb, "thetaEB":off,
            "detBlock":block_det, "difference":te-tb,
            "inverseE":tb/block_det, "inverseB":te/block_det,
            "inverseEB":-off/block_det}


def response_derivatives(triads, H):
    """YM time derivatives of the three isotropic 2-form Gram coefficients."""
    me_dot = Q(2)*sum((t.electric*t.tangent(H)[1] for t in triads), Q(0))
    mb_dot = Q(2)*sum((t.magnetic*t.magnetic_dot(H) for t in triads), Q(0))
    mix_dot = sum((t.tangent(H)[1]*t.magnetic + t.electric*t.magnetic_dot(H)
                   for t in triads), Q(0))
    return me_dot, mb_dot, mix_dot


def target_Hdot_for_diagonal_matching(triads, beta, alpha, curvature=0):
    me, mb, _ = response_blocks(triads)
    beta, alpha, curvature = map(rat, (beta, alpha, curvature))
    if beta <= 0 or alpha <= 0:
        raise ValueError("positive couplings required")
    return curvature + alpha*(me-mb)/(2*beta)


def symmetric_two_triad_example():
    """Exact rational configuration with thetaE=thetaB and thetaEB=0.

    Hdot is algebraically selected to match the diagonal cone, rather than
    evolved from a gravitational field equation. YM dynamics break thetaEB=0.
    """
    h = Q(1); beta=Q(1,100); alpha=Q(3,50)
    psi=Q(1,4); e=Q(1,32); g=Q(1)
    triads=(Triad(psi,e,g), Triad(psi,-e,g))
    hdot = target_Hdot_for_diagonal_matching(triads,beta,alpha)
    response = induced_response(triads,h,hdot,beta,alpha)
    me,mb,mix = response_blocks(triads)
    _,_,mix_dot=response_derivatives(triads,h)
    assert response['difference']==0 and response['thetaEB']==0
    assert mix_dot == 2*g*psi*(me-mb)
    assert alpha*mix_dot == 4*beta*g*psi*hdot
    return {"triads":triads,"H":h,"Hdot":hdot,"beta":beta,"alpha":alpha,
            "me":me,"mb":mb,"mix":mix,"mixDot":mix_dot,
            "thetaMixDot":alpha*mix_dot,"theta":response}


def rk4_one_step(triads, H, Hdot, dt):
    """Exact-rational fourth-order step on a prescribed linear H(t)."""
    H, Hdot, dt = map(rat, (H,Hdot,dt))
    if dt <= 0:
        raise ValueError("positive step required")
    def tangent(psi,e,g,h):
        return (e-h*psi, -2*h*e-2*g*g*psi**3)
    out=[]
    for t in triads:
        x,e,g=t.psi,t.electric,t.coupling
        k1=tangent(x,e,g,H)
        k2=tangent(x+dt*k1[0]/2,e+dt*k1[1]/2,g,H+dt*Hdot/2)
        k3=tangent(x+dt*k2[0]/2,e+dt*k2[1]/2,g,H+dt*Hdot/2)
        k4=tangent(x+dt*k3[0],e+dt*k3[1],g,H+dt*Hdot)
        out.append(Triad(x+dt*(k1[0]+2*k2[0]+2*k3[0]+k4[0])/6,
                         e+dt*(k1[1]+2*k2[1]+2*k3[1]+k4[1])/6,g))
    return tuple(out)


if __name__ == '__main__':
    x=symmetric_two_triad_example()
    for k in ('Hdot','me','mb','mix','mixDot','thetaMixDot'):
        print(f'{k}={x[k]}')


def einstein_ym_tangent(triads, H, kappa):
    """Spatially-flat Einstein--Yang--Mills plus a constant Lambda.

    dot(H)=-kappa*(sum(E_i^2+B_i^2)), as rho+p=2*sum(E^2+B^2).
    This background is a separate GR consistency laboratory, not Lambda-GfE.
    """
    H, kappa = rat(H), rat(kappa)
    if kappa <= 0:
        raise ValueError("positive gravitational coupling required")
    hdot = -kappa * sum((t.electric**2 + t.magnetic**2 for t in triads), Q(0))
    return hdot, tuple(t.tangent(H) for t in triads)


def einstein_ym_lambda(triads, H, kappa):
    """Hamiltonian constraint 3 H^2=Lambda+kappa*rho."""
    return 3*rat(H)**2 -rat(kappa)*energy_pressure(triads)[0]


def instantaneous_gr_example():
    """Simultaneous GR Raychaudhuri and diagonal cone matching at one instant.

    beta=1/100, alpha=3/50, kappa=9/5, H=1, psi=1/4,
    E1=-E2=1/32, g1=g2=1, Lambda=3045/1024.
    """
    x=symmetric_two_triad_example()
    kappa=Q(9,5)
    hdot, _ = einstein_ym_tangent(x['triads'],x['H'],kappa)
    lam=einstein_ym_lambda(x['triads'],x['H'],kappa)
    rho, pressure=energy_pressure(x['triads'])
    me_dot, mb_dot, mix_dot=response_derivatives(x['triads'],x['H'])
    # The exact GR radiation continuity equation gives Hddot=-4 H Hdot.
    hddot=-4*x['H']*hdot
    match_dot=x['alpha']*(me_dot-mb_dot)-2*x['beta']*hddot
    assert hdot==x['Hdot']
    assert lam==Q(3045,1024)
    assert match_dot==0 and mix_dot!=0
    assert 3*x['H']**2==lam+kappa*rho
    return {**x,'kappa':kappa,'Lambda':lam,'rho':rho,'pressure':pressure,
            'Hddot':hddot,'matchDot':match_dot}


def einstein_ym_rk4_one_step(triads,H,kappa,dt):
    """One fully coupled rational RK4 step with H and gauge fields evolving.

    This follows the Einstein--Yang--Mills system, not full Lambda-GfE.
    """
    H,kappa,dt=map(rat,(H,kappa,dt))
    if dt<=0:
        raise ValueError("positive step required")
    state=(H,)+tuple(x for t in triads for x in (t.psi,t.electric))
    def F(s):
        h=s[0]
        tt=tuple(Triad(s[1+2*i],s[2+2*i],t.coupling) for i,t in enumerate(triads))
        dh, ds=einstein_ym_tangent(tt,h,kappa)
        return (dh,)+tuple(x for pair in ds for x in pair)
    def plus(s,d,c):
        return tuple(u+c*v for u,v in zip(s,d))
    k1=F(state)
    k2=F(plus(state,k1,dt/2))
    k3=F(plus(state,k2,dt/2))
    k4=F(plus(state,k3,dt))
    result=tuple(s+dt*(a+2*b+2*c+d)/6 for s,a,b,c,d in zip(state,k1,k2,k3,k4))
    return result[0],tuple(Triad(result[1+2*i],result[2+2*i],t.coupling)
                           for i,t in enumerate(triads))


def raw_riemann_pair_response(triads, lambda_coupling=1):
    """6x6 derivative of S_int=(lambda/4) R_abcd sum(F^ab F^cd).

    Each unique antisymmetric pair appears twice in the covariant contraction,
    hence the derivative w.r.t. independent ordered-pair matrix R_IJ is
    lambda*sum(F^I F^J). Pair index order: (01,02,03,23,31,12).
    F^0i=-E_i in signature (-+++), F^jk=B_i. The Riemann first Bianchi
    identity needs a separate algebraic projection; this is the *raw* response.
    Full metric variation of S_int is not included in the minimal YM stress.
    """
    lam=rat(lambda_coupling)
    m=[[Q(0) for _ in range(6)] for _ in range(6)]
    for t in triads:
        for a in range(3):
            basis=[Q(0)]*6
            basis[a]=-t.electric
            basis[a+3]=t.magnetic
            for i in range(6):
                for j in range(6):
                    m[i][j]+=lam*basis[i]*basis[j]
    return tuple(tuple(row) for row in m)


def reference_experiment():
    """Compact exact synthetic receipt for the GR+YM matching counterexample."""
    x=instantaneous_gr_example()
    dt=Q(1,10000)
    h1,ts1=einstein_ym_rk4_one_step(x['triads'],x['H'],x['kappa'],dt)
    r1=response_blocks(ts1)
    hdot1,_=einstein_ym_tangent(ts1,h1,x['kappa'])
    theta1=induced_response(ts1,h1,hdot1,x['beta'],x['alpha'])
    return {
        "schema":"mathcan.toe08.yang_mills.v1",
        "status":"synthetic GR+Yang-Mills demonstration; assumed observer-frame GfE map",
        "source":{
            "Pereira":"https://arxiv.org/abs/2609.03082",
            "Bianconi":"https://arxiv.org/abs/2610.34496",
            "YangMills":"https://arxiv.org/abs/1102.1932"},
        "couplings":{"alpha":str(x['alpha']),"beta":str(x['beta']),
                     "kappa":str(x['kappa']),"Lambda":str(x['Lambda']),
                     "g1":"1","g2":"1"},
        "initial":{"H":str(x['H']),"Hdot":str(x['Hdot']),
                   "psi1":"1/4","psi2":"1/4","E1":"1/32","E2":"-1/32",
                   "rho":str(x['rho']),"pressure":str(x['pressure']),
                   "mE":str(x['me']),"mB":str(x['mb']),"mixed":str(x['mix']),
                   "mixedDot":str(x['mixDot']),"thetaMixedDot":str(x['thetaMixDot']),
                   "diagonalMatchDot":str(x['matchDot'])},
        "one_step":{"dt":str(dt),"mixed_sign":(-1 if r1[2]<0 else 1 if r1[2]>0 else 0),
                    "diagonal_match_abs_lt":"1/10000000",
                    "friedmann_residual_abs_lt":"1/1000000000000000",
                    "thetaMixedSign":(-1 if theta1['thetaEB']<0 else 1)},
        "verified_source_equation_scope":"Yang--Mills + Einstein background only; no GfE coupled field equations"
    }
