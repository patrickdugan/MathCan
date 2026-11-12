"""TOE-13: exact algebraic elimination of the independent auxiliary G-field.

For an invertible positive-background real matrix Theta, the first-order
Legendre functional L(G,Theta)=-Tr(G Theta)+Tr(log G)+n has stationary
G=Theta^{-1} and on-shell L=-log det Theta. This is a local algebraic
identity and the Schur derivative of the G sector. It does not solve the
covariant connection, metric, matter or gauge constraint PDE.
"""
from fractions import Fraction as F
from .mixed_principal import det,rat


def mm(a,b):
    if not a or not b or len(a[0])!=len(b):raise ValueError('incompatible matrices')
    return tuple(tuple(sum((rat(a[i][k])*rat(b[k][j]) for k in range(len(b))),F())
                       for j in range(len(b[0]))) for i in range(len(a)))


def trace(a):
    if not a or any(len(r)!=len(a) for r in a):raise ValueError('square required')
    return sum((rat(a[i][i]) for i in range(len(a))),F())


def inverse(a):
    n=len(a)
    if not n or any(len(r)!=n for r in a):raise ValueError('square required')
    m=[[rat(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        p=next((i for i in range(j,n) if m[i][j]),None)
        if p is None:raise ValueError('singular auxiliary metric')
        m[p],m[j]=m[j],m[p]
        v=m[j][j];m[j]=[x/v for x in m[j]]
        for k in range(n):
            if j==k:continue
            v=m[k][j]
            m[k]=[x-v*y for x,y in zip(m[k],m[j])]
    return tuple(tuple(row[n:]) for row in m)


def scale(a,s):return tuple(tuple(rat(s)*rat(x) for x in row) for row in a)


def symmetry_bilinear(theta,dtheta1,dtheta2):
    """Schur of independent G variations, checked against direct on-shell Hessian."""
    n=len(theta)
    if any(len(x)!=n for x in theta) or any(len(x)!=n for x in dtheta1) or any(len(x)!=n for x in dtheta2):
        raise ValueError('matching square matrices required')
    J=inverse(theta)
    def perturb(D):return scale(mm(mm(J,D),J),-1)
    k1,k2=perturb(dtheta1),perturb(dtheta2)
    first=-trace(mm(k1,dtheta2))-trace(mm(k2,dtheta1))
    second=-trace(mm(mm(mm(theta,k1),theta),k2))
    schur=first+second
    direct=trace(mm(mm(mm(J,dtheta1),J),dtheta2))
    if direct!=schur:raise AssertionError('auxiliary Schur mismatch')
    return {'stationary_dG1':k1,'stationary_dG2':k2,
            'first':first,'second':second,'schur':schur,'direct':direct,
            'G_background':J}


def diagonal_vector_hessian(theta_t,theta_s,dricci,beta):
    """Exact auxiliary Schur with a frozen background vector-Ricci operator.

    dRicci is a covariant 4x4 matrix; raise its first Lorentzian index.
    """
    theta_t,theta_s,beta=map(rat,(theta_t,theta_s,beta))
    if theta_t<=0 or theta_s<=0:raise ValueError('positive diagonal background')
    signature=(-1,1,1,1)
    theta=tuple(tuple((theta_t if i==0 else theta_s) if i==j else F()
                      for j in range(4)) for i in range(4))
    d=tuple(tuple(-beta*signature[i]*rat(dricci[i][j]) for j in range(4)) for i in range(4))
    return symmetry_bilinear(theta,d,d)['direct']

if __name__=='__main__':
    from .form_sector_principal import linearized_ricci,metric_tensor_mode,background_denominators
    z=linearized_ricci((F(2),0,0,1),metric_tensor_mode())[0]
    th=background_denominators(F(2,5),1,F(1,100))
    print(diagonal_vector_hessian(th[1],th[2],z,F(1,100)))
