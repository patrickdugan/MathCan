"""OLM-07: exact-rational finite causal Grams and nonlinear remainder controls.

No numpy, torch, model checkpoint or nonstandard dependencies. The general
matrix/Taylor theorems are proved in OLM07_CAUSAL_GRAM_QUOTIENT.md; this oracle
checks rational instances and explicit sharp counterexamples.
"""
from fractions import Fraction
from itertools import product

ZERO=Fraction(0)
ONE=Fraction(1)


def q(x):
    return Fraction(x)


def transpose(mat):
    return tuple(tuple(mat[i][j] for i in range(len(mat)))
                 for j in range(len(mat[0])))


def multiply(a,b):
    if not a or not b or len(a[0])!=len(b):
        raise ValueError('incompatible matrix dimensions')
    bt=transpose(b)
    return tuple(tuple(sum((u*v for u,v in zip(row,col)),ZERO)
                       for col in bt) for row in a)


def causal_gram(jacobians,weights,dictionary):
    if len(jacobians)!=len(weights) or not jacobians:
        raise ValueError('positive finite family required')
    if any(w<=0 for w in weights) or sum(weights,ZERO)!=ONE:
        raise ValueError('weights must be positive and normalized')
    n=len(dictionary)
    m=len(dictionary[0])
    out=[[ZERO for _ in range(m)] for _ in range(m)]
    for J,w in zip(jacobians,weights):
        if any(len(row)!=n for row in J):
            raise ValueError('Jacobian input dimension mismatch')
        A=multiply(J,dictionary)
        term=multiply(transpose(A),A)
        for i in range(m):
            for j in range(m):
                out[i][j]+=w*term[i][j]
    return tuple(tuple(row) for row in out)


def energy(C,z):
    if len(C)!=len(z):
        raise ValueError('code dimension mismatch')
    return sum((z[i]*C[i][j]*z[j]
                for i in range(len(z)) for j in range(len(z))),ZERO)


def witness():
    w=(Fraction(1,3),Fraction(2,3))
    J=(
        ((ONE,ZERO,ZERO),(ZERO,ONE,ZERO)),
        ((ONE,ONE,ZERO),),
    )
    D=(
        (ONE,ZERO,Fraction(1,2),ONE),
        (ZERO,ONE,ONE,ZERO),
        (ZERO,ZERO,ONE,Fraction(2)),
    )
    Q=(
        (ZERO,ZERO,ZERO,ZERO),
        (ZERO,ZERO,ZERO,ZERO),
        (Fraction(9),Fraction(-3),Fraction(5,7),Fraction(4)),
    )
    plus=tuple(tuple(D[i][j]+Q[i][j] for j in range(4))
               for i in range(3))
    C=causal_gram(J,w,D)
    assert causal_gram(J,w,plus)==C
    src=(2,0,3,1)
    signs=(ONE,ONE,-ONE,ONE)
    changed=tuple(tuple(signs[j]*D[i][src[j]] for j in range(4))
                  for i in range(3))
    C2=causal_gram(J,w,changed)
    for i in range(4):
        for j in range(4):
            assert C2[i][j]==signs[i]*signs[j]*C[src[i]][src[j]]
    for z in product((-2,-1,0,1,2),repeat=4):
        zz=tuple(map(Fraction,z))
        assert energy(C,zz)>=ZERO
        zz_relabel=tuple(signs[j]*zz[src[j]] for j in range(4))
        assert energy(C2,zz_relabel)==energy(C,zz)
    return {'causal_gram':[[str(x) for x in row] for row in C],
            'gauge_columns_added':4,
            'signed_permutation_gram_congruence':True,
            'psd_nonnegative_samples':625}


def nonlinear_quadratic_F(x,y,a=Fraction(2)):
    return x+a*y*y/2


def finite_radius_witness(radius,a=Fraction(2)):
    r=q(radius)
    if r<=0:
        raise ValueError('positive radius required')
    M=abs(a);L=ONE
    d0=(nonlinear_quadratic_F(r,ZERO,a)-nonlinear_quadratic_F(ZERO,ZERO,a))/r
    d1=(nonlinear_quadratic_F(ZERO,r,a)-nonlinear_quadratic_F(ZERO,ZERO,a))/r
    delta=(d0,d1)
    true=(ONE,ZERO)
    C=((ONE,ZERO),(ZERO,ZERO))
    Chat=tuple(tuple(delta[i]*delta[j] for j in range(2)) for i in range(2))
    bound=M*L*r+M*M*r*r/4
    assert all(abs(Chat[i][j]-C[i][j])<=bound
               for i in range(2) for j in range(2))
    assert nonlinear_quadratic_F(ZERO,r,a)-nonlinear_quadratic_F(ZERO,ZERO,a) == a*r*r/2
    return {'radius':str(r),'a':str(a),'bound_each_entry':str(bound),
            'true_gram':[[str(x) for x in row] for row in C],
            'finite_difference_gram':[[str(x) for x in row] for row in Chat],
            'linear_gauge_direction_finite_effect':str(a*r*r/2),
            'quadratic_remainder_bound_sharp':abs(a*r*r/2)==M*r*r/2}


def contrasting_errors(bad_hidden=Fraction(100),good_hidden=Fraction(1,10)):
    """For F(x,y)=x, large (0,N) error is causally zero."""
    if bad_hidden<=good_hidden or good_hidden<=0:
        raise ValueError('require 0<eps<N')
    return {'hidden_norm_squared_large_error':str(bad_hidden**2),
            'output_squared_error_of_large_error':'0',
            'hidden_norm_squared_small_error':str(good_hidden**2),
            'output_squared_error_of_small_error':str(good_hidden**2)}


if __name__=='__main__':
    import json
    print(json.dumps({'linear':witness(),
                      'nonlinear':[finite_radius_witness(Fraction(1,2)),
                                   finite_radius_witness(Fraction(1,8)),
                                   finite_radius_witness(Fraction(1,32))],
                      'ranking':contrasting_errors()},indent=2))
