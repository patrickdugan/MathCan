"""TOE-15: SO(2) tensor closure in a declared SU(2)^2 trial, and an
independent foundational two-multiplet curvature-response witness.

Scope:
(A) Exact Fourier-real algebra of the preexisting TOE-13 6x6 *trial*
    tensor bilinear, with SO(2) spin-two equivariance and 3x3 Hermitian
    helicity reduction. This tests a necessary tensor-sector closure
    condition. It is not a complete source-normalized GfE Cauchy system.
(B) A separate source-structured, algebraic two-multiplet rank witness
    for Pereira's Eq. (40), built from two rank<=2 outer-product
    contributions on the bivector space. It does not solve the field
    equations, assert that its jets are realizable, or supply a coupled
    perturbation operator.
"""
from __future__ import annotations
from fractions import Fraction as F

from .mixed_principal import det,rat
from .tensor_subspace import at_frequency,default_params,_fit_polynomial
from .form_sector_principal import augmented_coefficients
from .cone_matching import cone_certificate


def _matmul(a,b):
    n=len(a)
    if not n or any(len(row)!=len(a[0]) for row in a):
        raise ValueError('rectangular first matrix expected')
    if len(a[0])!=len(b) or not b or any(len(row)!=len(b[0]) for row in b):
        raise ValueError('incompatible second matrix')
    return tuple(tuple(sum((rat(a[i][k])*rat(b[k][j]) for k in range(len(b))),F())
                       for j in range(len(b[0]))) for i in range(n))


def _rank(a):
    if not a or any(len(row)!=len(a[0]) for row in a):
        raise ValueError('nonempty rectangular matrix required')
    m=[[rat(z) for z in row] for row in a]
    n=len(m);k=len(m[0]);j=0;r=0
    while j<k and r<n:
        pivot=next((i for i in range(r,n) if m[i][j]),None)
        if pivot is None:
            j+=1
            continue
        m[pivot],m[r]=m[r],m[pivot]
        v=m[r][j]
        for x in range(j,k):m[r][x]/=v
        for i in range(r+1,n):
            v=m[i][j]
            for x in range(j,k):m[i][x]-=v*m[r][x]
        r+=1;j+=1
    return r


def spin_two_generator():
    """J_6=diag(J_2,J_2,J_2), J_2=[[0,-1],[1,0]]."""
    return tuple(tuple(F(1 if j==i-1 and i%2==1 else
                          -1 if j==i+1 and i%2==0 else 0)
                       for j in range(6)) for i in range(6))


def equivariance_certificate(m):
    """Check [P,J]=0, P=P^T, with independent 2x2 block checks.

    A 3x3 complex Hermitian reduction then exists for this particular P.
    """
    if len(m)!=6 or any(len(row)!=6 for row in m):
        raise ValueError('six tensor amplitudes required')
    m=tuple(tuple(rat(v) for v in row) for row in m)
    if any(m[i][j]!=m[j][i] for i in range(6) for j in range(6)):
        raise ValueError('real symmetric tensor Hessian required')
    j=spin_two_generator()
    lhs=_matmul(m,j);rhs=_matmul(j,m)
    if lhs!=rhs:
        raise AssertionError('trial tensor block fails SO(2) equivariance')
    for f in range(3):
        for g in range(3):
            x,y=2*f,2*g
            if m[x][y]!=m[x+1][y+1] or m[x][y+1]!=-m[x+1][y]:
                raise AssertionError('non-complex-linear tensor block')
    return True


def _cadd(a,b):return (a[0]+b[0],a[1]+b[1])
def _cneg(a):return (-a[0],-a[1])
def _csub(a,b):return _cadd(a,_cneg(b))
def _cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def _cconj(a):return (a[0],-a[1])


def helicity_hermitian(m):
    """Real 6x6 matrix -> Hermitian 3x3 over Gaussian rationals.

    Complex coordinate z_f=q_(f,+)+i q_(f,cross).
    Each 2x2 real block [[a,b],[-b,a]] corresponds to a-ib.
    """
    equivariance_certificate(m)
    h=tuple(tuple((rat(m[2*f][2*g]),rat(m[2*f+1][2*g]))
                  for g in range(3)) for f in range(3))
    for f in range(3):
        for g in range(3):
            if h[f][g]!=_cconj(h[g][f]):
                raise AssertionError('Hermitian conjugacy lost')
    return h


def det3_gaussian(h):
    if len(h)!=3 or any(len(row)!=3 for row in h):
        raise ValueError('three-by-three complex matrix required')
    a=_cmul(h[0][0],_csub(_cmul(h[1][1],h[2][2]),_cmul(h[1][2],h[2][1])))
    b=_cmul(h[0][1],_csub(_cmul(h[1][0],h[2][2]),_cmul(h[1][2],h[2][0])))
    c=_cmul(h[0][2],_csub(_cmul(h[1][0],h[2][1]),_cmul(h[1][1],h[2][0])))
    return _cadd(_csub(a,b),c)


def trial_tensor_six(omega,*,sigma1=F(1,100),params=None):
    params=default_params() if params is None else dict(params)
    coeff=augmented_coefficients(sigma1=rat(sigma1),**params)
    return at_frequency(coeff,rat(omega))


def trial_helicity_certificate(omega,*,sigma1=F(1,100),params=None):
    m=trial_tensor_six(omega,sigma1=sigma1,params=params)
    h=helicity_hermitian(m)
    d=det3_gaussian(h)
    if d[1]:
        raise AssertionError('Hermitian helicity determinant is not real')
    real_det=det(m)
    if real_det!=d[0]**2:
        raise AssertionError('real six-mode determinant fails helicity square')
    return {'omega':rat(omega),'helicity_determinant':d[0],
            'six_mode_determinant':real_det,'six_mode_det_square':True,
            'SO2_equivariant':True,'hermitian':True}


def trial_helicity_polynomial(*,sigma1=F(1,100),params=None):
    """Extract exact degree<=8 helicity polynomial by 9-point interpolation."""
    nodes=tuple(F(i) for i in range(-4,5))
    values=tuple(trial_helicity_certificate(x,sigma1=sigma1,params=params)['helicity_determinant']
                 for x in nodes)
    coeff=_fit_polynomial(nodes,values)
    # Degree bound 8 follows weights 4/2/2 and 3/3/2 of the 3x3 determinant.
    for x in (F(-9,2),F(-5,2),F(-1,3),F(2,5),F(11,3)):
        y=sum((c*x**i for i,c in enumerate(coeff)),F())
        if y!=trial_helicity_certificate(x,sigma1=sigma1,params=params)['helicity_determinant']:
            raise AssertionError('degree-eight interpolation failed')
    return coeff


def outer(v):
    v=tuple(map(rat,v))
    return tuple(tuple(v[i]*v[j] for j in range(len(v))) for i in range(len(v)))


def combine_outer(u,v,lam):
    """One foundational-type algebraic block |u><u| + lambda|v><v|."""
    lam=rat(lam)
    if len(u)!=6 or len(v)!=6:
        raise ValueError('bivector E/B six-space required')
    a,b=outer(u),outer(v)
    return tuple(tuple(a[i][j]+lam*b[i][j] for j in range(6)) for i in range(6))


def two_multiplet_witness():
    """Construct M=diag(0_3, 2I_3) from two rank-2 outer products.

    u1=u2=e_Bz, v1=e_Bx, v2=e_By, with common lambda=2.
    This is an algebraic constitutive witness, not a field solution.
    """
    ex=(F(0),F(0),F(0),F(1),F(0),F(0))
    ey=(F(0),F(0),F(0),F(0),F(1),F(0))
    ez=(F(0),F(0),F(0),F(0),F(0),F(1))
    m1=combine_outer(ez,ex,2)
    m2=combine_outer(ez,ey,2)
    total=tuple(tuple(m1[i][j]+m2[i][j] for j in range(6)) for i in range(6))
    expected=tuple(tuple(F(2) if i==j and i>=3 else F() for j in range(6))
                   for i in range(6))
    if total!=expected:
        raise AssertionError('rank-three isotropic bivector response mismatch')
    ranks=(_rank(m1),_rank(m2),_rank(total))
    if ranks!=(2,2,3):
        raise AssertionError('two-multiplet rank certificate mismatch')
    return {'m1':m1,'m2':m2,'combined':total,'individual_ranks':ranks[:2],
            'rank':ranks[2], 'mE':F(), 'mB':F(2), 'number_of_multiplets':2}


def source_response_match(*,alpha=F(3,500),beta=F(1,100),
                          accel=F(2,5),spatial=1,mE=0,mB=2):
    """Pereira (2026), Eq. (39)-(40), on diagonal E/B positive response."""
    alpha,beta,accel,spatial,mE,mB=map(rat,(alpha,beta,accel,spatial,mE,mB))
    if alpha<=0 or beta<=0:
        raise ValueError('positive alpha and beta required')
    te=1+alpha*mE-2*beta*accel
    tb=1+alpha*mB-2*beta*spatial
    ts=1-beta*(accel+2*spatial)
    if min(te,tb,ts)<=0:
        raise ValueError('positive source response required')
    compensation=alpha*(mE-mB)-2*beta*(accel-spatial)
    if (te==tb)!=(compensation==0):
        raise AssertionError('matter-curvature cone identity broken')
    we,wb,ws=1/te,1/tb,1/ts
    q=cone_certificate(ws*ws/2,2*we*we,F(1),wb/we)
    # The source vacuum two-square form with dressed diagonal E/B response.
    return {'thetaE':te,'thetaB':tb,'thetaS':ts,
            'WE':we,'WB':wb,'Ws':ws,'compensation_residual':compensation,
            'cone_matched':te==tb,'discriminant':q['discriminant'],
            'complex_frequency_pair':q['discriminant']<0,
            'x_roots_approx':q['roots_approx']}


def reference_experiment():
    w=two_multiplet_witness()
    matched=source_response_match(mE=w['mE'],mB=w['mB'])
    shifted=source_response_match(mB=F(201,100))
    if not matched['cone_matched'] or matched['thetaE']!=F(124,125):
        raise AssertionError('reference compensated source tensor cone must match')
    if shifted['cone_matched'] or shifted['discriminant']>=0:
        raise AssertionError('nonzero matter detuning must split cone pair')
    coeff=trial_helicity_polynomial()
    return {'schema':'mathcan.toe15.helicity.v1',
            'source_two_multiplet_algebraic_rank':w['rank'],
            'source_two_multiplet_individual_ranks':list(w['individual_ranks']),
            'source_theta_E':str(matched['thetaE']),
            'source_theta_B':str(matched['thetaB']),
            'source_reference_cone_matched':matched['cone_matched'],
            'source_detuned_discriminant':str(shifted['discriminant']),
            'trial_SO2_equivariant':True,
            'trial_hermitian_helicity_degree':max(i for i,c in enumerate(coeff) if c),
            'trial_helicity_polynomial_even':all(not c for i,c in enumerate(coeff) if i%2),
            'trial_restricted_six_determinant_is_square':True,
            'source_multiplet_jet_integrability_verified':False,
            'source_multiplet_background_equations_solved':False,
            'complete_constrained_GfE_YM_tensor_system_derived':False,
            'strong_hyperbolicity_verified':False}


if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),sort_keys=True,indent=2))
