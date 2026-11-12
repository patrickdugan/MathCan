"""TOE-16: source two-form matter kinetic Hessian and multiplet-rank gate.

Grounded in Bianconi's M_p=Sum_i[(D Phi_i)_p (D Phi_i)_p^*
+ lambda (Phi_i)_p (Phi_i)_p^*] and Pereira's E/B response matching.
We isolate the magnetic three-space with positive scalar response theta_B;
the one-form perturbations supply delta u_i=(d delta omega_i)_B. Their
pure static transverse-curl fluctuations have zero scalar-sector divergence
and no one-form-sector D Phi variation when delta Phi_0=delta Phi_2=0.

This is the exactly specified frozen two-form source sub-Hessian, with
lambda held fixed and no metric variation unless explicitly requested.
It is NOT a complete gauge-fixed GfE tensor pencil, an on-shell FLRW
background or a physical hyperbolicity test.
"""
from __future__ import annotations
from fractions import Fraction as F
from .mixed_principal import det, rat
from .tensor_subspace import _fit_polynomial
from .helicity_constraint import _rank
from .operator_principal import wave_riemann_pair, wave_field_strength
from .auxiliary_g_schur import inverse

def v3(a):
    if len(a)!=3:raise ValueError("3-vector required")
    return tuple(map(rat,a))

def dot(a,b):
    return sum((x*y for x,y in zip(v3(a),v3(b))),F())

def identity3():
    return tuple(tuple(F(i==j) for j in range(3)) for i in range(3))

def outer3(a,b=None):
    a=v3(a); b=a if b is None else v3(b)
    return tuple(tuple(x*y for y in b) for x in a)

def madd(a,b):
    return tuple(tuple(x+y for x,y in zip(row,other)) for row,other in zip(a,b))

def scale(a,s):
    return tuple(tuple(rat(s)*x for x in row) for row in a)

def transpose(a):
    return tuple(zip(*a))

def matmul(a,b):
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(len(b))),F())
                       for j in range(len(b[0]))) for i in range(len(a)))

def tr(a):
    return sum((a[i][i] for i in range(len(a))),F())

def gram3(vectors):
    s=scale(identity3(),0)
    for v in vectors:
        s=madd(s,outer3(v))
    return s

def is_scalar_identity3(a):
    return all(a[i][j]==(a[0][0] if i==j else 0)
               for i in range(3) for j in range(3))

def witness_two():
    ez=(0,0,1)
    return {'u':(ez,ez),'v':((1,0,0),(0,1,0)), 'lam':F(2)}

def witness_three():
    """SO(3)-flavor-locked candidate U=I, V=I, lambda=1, M_B=2I."""
    e=((1,0,0),(0,1,0),(0,0,1))
    return {'u':e,'v':e,'lam':F(1)}

def check_witness(w):
    u=tuple(map(v3,w['u']));v=tuple(map(v3,w['v']))
    lam=rat(w['lam'])
    if len(u)!=len(v) or not u or lam<=0:
        raise ValueError('positive lambda and matched multiplets required')
    U=gram3(u);V=gram3(v)
    M=madd(U,scale(V,lam))
    if not is_scalar_identity3(M) or M[0][0]<=0:
        raise ValueError('positive isotropic magnetic response required')
    return {'U':U,'V':V,'M':M,'mB':M[0][0],'rankU':_rank(U),
            'rankV':_rank(V),'rankM':_rank(M),'n':len(u)}

def theta_magnetic(w,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    alpha,beta,spatial=map(rat,(alpha,beta,spatial))
    if alpha<=0 or beta<=0:raise ValueError('positive response parameters required')
    b=check_witness(w)
    theta=1+alpha*b['mB']-2*beta*spatial
    if theta<=0:raise ValueError('positive thetaB required')
    return theta

def theta_matrix_at(w, perturb, t,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Exactly quadratic source response in perturbation t of d omega_i."""
    u=tuple(map(v3,w['u']));v=tuple(map(v3,w['v']))
    perturb=tuple(map(v3,perturb))
    if len(perturb)!=len(u):raise ValueError('one perturbation per multiplet')
    m=scale(identity3(),0)
    for ui,vi,ai in zip(u,v,perturb):
        moved=tuple(x+rat(t)*a for x,a in zip(ui,ai))
        m=madd(m,outer3(moved))
        m=madd(m,scale(outer3(vi),w['lam']))
    base=1-2*rat(beta)*rat(spatial)
    return madd(scale(identity3(),base),scale(m,rat(alpha)))

def source_kinetic_hessian(w,perturb,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Direct trace-log second variation: tr(W D W D)-tr(W D2).

    D=alpha Sum_i(u_i a_i^T+a_i u_i^T),
    D2=2alpha Sum_i a_i a_i^T.
    """
    u=tuple(map(v3,w['u']))
    aa=tuple(map(v3,perturb))
    if len(u)!=len(aa):raise ValueError('wrong multiplet count')
    theta=theta_magnetic(w,alpha=alpha,beta=beta,spatial=spatial)
    inv=F(1)/theta
    d=scale(identity3(),0)
    for ui,a in zip(u,aa):
        d=madd(d,outer3(ui,a));d=madd(d,outer3(a,ui))
    aa2=gram3(aa)
    alpha=rat(alpha)
    return alpha**2*inv**2*tr(matmul(d,d))-2*alpha*inv*tr(aa2)

def determinant_hessian_oracle(w,perturb,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Independent exact determinant-polynomial second derivative of -log det.

    det(Theta(t)) has degree at most six since Theta entries are
    degree-two polynomials in t. Interpolate at seven rational nodes.
    """
    nodes=(F(-3),F(-2),F(-1),F(),F(1),F(2),F(3))
    values=tuple(det(theta_matrix_at(w,perturb,t,alpha=alpha,beta=beta,spatial=spatial))
                 for t in nodes)
    coeff=_fit_polynomial(nodes,values)
    d0,d1,d2=coeff[:3]
    if d0<=0:raise AssertionError('source baseline has nonpositive determinant')
    for t in (F(-5,2),F(5,3)):
        predicted=sum((v*t**j for j,v in enumerate(coeff)),F())
        actual=det(theta_matrix_at(w,perturb,t,alpha=alpha,beta=beta,spatial=spatial))
        if predicted!=actual:raise AssertionError('nonquadratic source response polynomial')
    return d1*d1/(d0*d0)-2*d2/d0

def flavor_trace_matrix(w,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Trace over independent multiplet flavor of the magnetic curl Hessian.

    T_ab = 2 (alpha W)^2 (tr U delta_ab+U_ab)
           -2 N (alpha W) delta_ab.
    The rotational anisotropy is proportional to traceless U.
    """
    c=rat(alpha)/theta_magnetic(w,alpha=alpha,beta=beta,spatial=spatial)
    U=check_witness(w)['U'];n=len(w['u']);trU=tr(U)
    return tuple(tuple(2*c*c*((trU if i==j else F())+U[i][j])
                       -(2*n*c if i==j else F())
                       for j in range(3)) for i in range(3))

def flavor_trace_independent(w,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Polarize direct Hessian, summing one-flavor blocks independently."""
    n=len(w['u']);basis=identity3()
    def q(i,a):
        aa=[(F(),F(),F()) for _ in range(n)]
        aa[i]=a
        return source_kinetic_hessian(w,aa,alpha=alpha,beta=beta,spatial=spatial)
    out=[[F() for _ in range(3)] for _ in range(3)]
    for i in range(n):
        for x in range(3):
            out[x][x]+=q(i,basis[x])
            for y in range(x+1,3):
                v=tuple(basis[x][j]+basis[y][j] for j in range(3))
                h=(q(i,v)-q(i,basis[x])-q(i,basis[y]))/2
                out[x][y]+=h;out[y][x]+=h
    return tuple(tuple(row) for row in out)

def rank_gate(w):
    """Necessary dynamic isotropy test within the source curl subblock."""
    c=check_witness(w)
    U=c['U'];T=flavor_trace_matrix(w)
    if c['n']<3 and c['rankM']==3 and c['rankU']==0:
        raise AssertionError('two rank<=2 multiplets cannot span rank three')
    return {'multiplets':c['n'],'rank_M':c['rankM'],'rank_U':c['rankU'],
            'M_isotropic':is_scalar_identity3(c['M']),
            'U_isotropic':is_scalar_identity3(U),
            'curl_flavor_trace_isotropic':is_scalar_identity3(T),
            'trace_kinetic':T,
            'necessary_rank_gate':c['n']>=3 or not is_scalar_identity3(T)}

def static_magnetic_mixing(w,xi,h,oneform,*,flavor=0,
                           alpha=F(3,500),beta=F(1,100),spatial=1):
    """Curvature-one-form highest-order trace-log cross Hessian.

    Only magnetic 2-form response is included, at omega=0.
    deltaTheta_R=-beta deltaR_(2), deltaTheta_M=alpha deltaM_(2)
    with u=(D Phi)_2 and delta u=d(delta omega).
    """
    xi=tuple(map(rat,xi))
    if len(xi)!=4 or xi[0]!=0:raise ValueError('static spatial covector required')
    if flavor<0 or flavor>=len(w['u']):raise ValueError('flavor index')
    d=wave_field_strength(xi,oneform)
    bvec=tuple(d[3:])
    if any(d[:3]):raise AssertionError('static curl has unexpected electric response')
    R=wave_riemann_pair(xi,h)
    rb=tuple(tuple(R[i+3][j+3] for j in range(3)) for i in range(3))
    u=v3(w['u'][flavor])
    dm=madd(outer3(u,bvec),outer3(bvec,u))
    wb=1/theta_magnetic(w,alpha=alpha,beta=beta,spatial=spatial)
    cross=-rat(alpha)*rat(beta)*wb**2*tr(matmul(rb,dm))
    return {'curvature_magnetic':rb,'curl_magnetic':bvec,
            'matter_first_variation':dm,'mixed_H':cross}

def rotate_flavor_locked(perturb,R):
    """For three triplet multiplets, delta U -> R delta U R^T."""
    if len(perturb)!=3 or len(R)!=3:
        raise ValueError('triplet and spatial rotation required')
    R=tuple(tuple(map(rat,row)) for row in R)
    if any(len(row)!=3 for row in R):raise ValueError('3x3 rotation required')
    if matmul(R,transpose(R))!=identity3():
        raise ValueError('rational orthogonal rotation required')
    U=transpose(tuple(v3(x) for x in perturb))
    out=matmul(matmul(R,U),transpose(R))
    return tuple(tuple(out[j][i] for j in range(3)) for i in range(3))

def triplet_irrep_hessian(perturb,*,alpha=F(3,500),beta=F(1,100),spatial=1):
    """Exact diagonal-SO(3) decomposition 3⊗3 = 1 ⊕ 3 ⊕ 5.

    The variation matrix A has columns delta u_i, and the triplet
    locked background has U=I. Decompose A into trace scalar,
    antisymmetric vector and symmetric-traceless spin-2 parts.
    The source log Hessian is
      (4c²-2c)(||scalar||²+||spin2||²)-2c||vector||²,
    c=alpha/thetaB. This is an algebraic curl-channel result.
    """
    if len(perturb)!=3:raise ValueError("triplet required")
    A=transpose(tuple(v3(z) for z in perturb))
    At=transpose(A)
    S=scale(madd(A,At),F(1,2))
    K=scale(madd(A,scale(At,-1)),F(1,2))
    scalar=scale(identity3(),tr(A)/3)
    spin2=madd(S,scale(scalar,-1))
    def norm2(x):return sum((z*z for row in x for z in row),F())
    scalar_norm=norm2(scalar);vector_norm=norm2(K);spin2_norm=norm2(spin2)
    if norm2(A)!=scalar_norm+vector_norm+spin2_norm:
        raise AssertionError("SO3 decomposition fails orthogonality")
    c=rat(alpha)/theta_magnetic(witness_three(),alpha=alpha,beta=beta,spatial=spatial)
    hs=4*c*c-2*c
    hv=-2*c
    derived=hs*(scalar_norm+spin2_norm)+hv*vector_norm
    direct=source_kinetic_hessian(witness_three(),perturb,alpha=alpha,beta=beta,spatial=spatial)
    if derived!=direct:
        raise AssertionError("irrep-resolved source kinetic Hessian mismatch")
    return {'scalar_trace':tr(A),'scalar_norm':scalar_norm,
            'vector_norm':vector_norm,'spin2_norm':spin2_norm,
            'spin2_matrix':spin2,'spin2_coefficient':hs,
            'vector_coefficient':hv,'hessian':derived}


def triplet_spin_two_polarizations():
    """Magnetic curl matrices with only + and × helicity-2 amplitudes.

    Along p_z=1 these are realized by transverse one-form fluctuations.
    The first row index is magnetic x/y/z; columns are triplet flavors.
    """
    plus=((F(1),F(),F()),(F(),F(-1),F()),(F(),F(),F()))
    cross=((F(),F(1),F()),(F(1),F(),F()),(F(),F(),F()))
    return tuple(tuple(tuple(m[j][i] for j in range(3)) for i in range(3))
                 for m in (plus,cross))


def triplet_static_spin2_mixing():
    """Explicit h(+/cross) to flavor-locked one-form spin-two mixing.

    Uses p_z=1, and the two independent TT metric polarizations. Each
    triplet spin-two curl basis comes from two transverse one-form modes.
    The highest-derivative two-form source cross Hessian is diagonal
    and nonzero: -4 alpha beta W_B^2 for each helicity. This is one
    source principal subblock, not a physical Cauchy characteristic.
    """
    w=witness_three()
    k=(F(),F(),F(),F(1))
    hp=[[F() for _ in range(4)] for _ in range(4)]
    hp[1][1]=F(1);hp[2][2]=F(-1)
    hx=[[F() for _ in range(4)] for _ in range(4)]
    hx[1][2]=hx[2][1]=F(1)
    z=(F(),)*4
    aplus=((F(),F(),F(-1),F()),(F(),F(-1),F(),F()),z)
    across=((F(),F(1),F(),F()),(F(),F(),F(-1),F()),z)
    rows=[]
    for h in (hp,hx):
        row=[]
        for amps in (aplus,across):
            row.append(sum((static_magnetic_mixing(w,k,h,a,flavor=i)['mixed_H']
                            for i,a in enumerate(amps)),F()))
        rows.append(tuple(row))
    result=tuple(rows)
    expected=-4*F(3,500)*F(1,100)*(F(125,124)**2)
    if result!=((expected,F()),(F(),expected)):
        raise AssertionError("source helicity-two cross mixing mismatch")
    return {'mixed_helicity_matrix':result, 'mixed_coefficient':expected,
            'helicity_plus_cross_mixing':F(),
            'only_two_form_source_principal':True}


def reference_experiment():
    w2=witness_two();w3=witness_three()
    spin2=triplet_irrep_hessian(triplet_spin_two_polarizations()[0])
    mixed=triplet_static_spin2_mixing()
    delta=source_kinetic_hessian(w2,((0,0,1),(0,0,0))) - source_kinetic_hessian(w2,((0,1,0),(0,0,0)))
    expected=2*(F(3,500)/F(124,125))**2
    if delta!=expected or delta!=F(9,123008):
        raise AssertionError('exact kinetic anisotropy identity failed')
    if not rank_gate(w2)['necessary_rank_gate'] or not rank_gate(w3)['curl_flavor_trace_isotropic']:
        raise AssertionError('multiplet rank gate failed')
    return {'schema':'mathcan.toe16.multiplet_kinetic.v1',
            'two_multiplet_thetaB':str(theta_magnetic(w2)),
            'two_multiplet_parallel_perpendicular_gap':str(delta),
            'two_multiplet_curl_trace_isotropic':False,
            'three_multiplet_M_B':str(check_witness(w3)['mB']),
            'three_multiplet_spin2_kinetic_coefficient':str(spin2['spin2_coefficient']),
            'three_multiplet_helicity2_variables_present':spin2['spin2_norm']>0,
            'three_multiplet_static_spin2_metric_matter_mixing':str(mixed['mixed_coefficient']),
            'three_multiplet_curl_trace_isotropic':True,
            'full_principal_isotropy_verified':False,
            'full_metric_matter_kinetic_derived':False,
            'source_background_equations_solved':False,
            'physical_constraints_eliminated':False,
            'strong_hyperbolicity_verified':False}

if __name__=='__main__':
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
