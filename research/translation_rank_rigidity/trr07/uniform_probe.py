#!/usr/bin/env python3
"""Exact identities for the uniform order>=19 interpolation exclusion.

The accompanying uniform_probe.md supplies the divisor/residue argument.
This script verifies its integer polynomial identities and independently checks
local coefficients and the addition law on finite-field fixtures.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import sympy as sp

from finite_fields import Field, Curve, prime, residue_profile


def polynomial_certificate():
    X,A,B,c,n=sp.symbols('X A B c n')
    F=X**3+A*X+B; R=3*X**2+A
    K=sp.Poly(sp.expand((4*(6*X+3*c)*F+(n-1)*R**2)**2
                        -64*n*(X+c)*R**2*F),X)
    C={i:sp.expand(K.nth(i)) for i in range(9)}
    identities={}
    def check(name,lhs,rhs):
        difference=sp.expand(lhs-rhs)
        assert difference==0,name
        identities[name]=str(sp.factor(lhs))+' = '+str(sp.factor(rhs))
    assert K.degree()==8
    check('leading_coefficient',C[8],9*(n-1)*(9*n-25))
    check('next_coefficient',C[7],-360*c*(n-1))
    Q=sp.expand((6*X+3*c)**2*F-4*(X+c)*R**2)
    check('n_equals_one_factorization',K.as_expr().subs(n,1),16*F*Q)
    Q3=sp.expand(Q).coeff(X,3);Q2=sp.expand(Q).coeff(X,2)
    check('n_equals_one_x3',Q3,12*A+9*c*c)
    check('n_equals_one_x2',Q2,12*A*c+36*B)
    check('n_equals_one_discriminant_ideal',48*(4*A**3+27*B**2),
          16*A*A*Q3+(Q2-24*A*c)*Q2)
    check('nine_n_equals_25_x7',C[7],-40*c*(9*n-25)-640*c)
    check('nine_n_equals_25_x6',3*C[6],
          4*A*(9*n-25)*(9*n-13)+320*A+432*c*c)
    check('nine_n_equals_25_x5',C[5],
          -24*A*c*(25*n-33)-16*B*(9*n-25)+320*B)
    # The elimination step retains an exact integer numerator.
    a,z=sp.symbols('a z')
    equation=4*a*z+6*X+3*c+(n-1)*z*z
    other=-4*a*z+6*X+3*c+(n-1)*z*z
    product=sp.expand(equation*other).subs(a*a,n*(X+c))
    rational=sp.together(product.subs(z,R/(2*sp.Symbol('y'))))
    y=sp.Symbol('y')
    numerator=sp.expand(rational*16*y**4)
    numerator=sp.rem(sp.Poly(numerator,y),sp.Poly(y*y-F,y)).as_expr()
    check('doubling_elimination_numerator',numerator,K.as_expr())
    return dict(ring='Z[n,c,A,B,X]',polynomial_degree=8,
                polynomial=str(K.as_expr()),coefficients_low_first=[str(C[i]) for i in range(9)],
                checked_integer_identities=identities,identity_count=len(identities),
                branch_constants={'n_equals_one':48,'nine_n_equals_25_c':640,
                                  'nine_n_equals_25_A':320,'nine_n_equals_25_B':320},
                characteristic_analysis={
                    '2':'outside the model; denominators and branch constants can vanish',
                    '3':'outside the model; short-coordinate and local-coefficient divisions use 3',
                    '5':'9n=25 implies n=0; this belongs to the separate characteristic-dividing argument',
                    'p_greater_than_3_and_n_nonzero':'every identity solution has 4A^3+27B^2=0',
                    'p_equals_subgroup_prime':'doubling forces a_P=0; logarithmic derivative kernel and a degree-one divisor give contradiction'})


def local_coefficients(C,seq):
    """Coefficients of 1/Phi(x(P+z)) from Taylor expansion through z^3."""
    F=C.F;n=len(seq); roots=[P[0] for P in seq[1:(n+1)//2]]
    a=[0];b=[0]
    for x,y in seq[1:]:
        inverse_differences=[F.inv(F.sub(x,v)) for v in roots if v!=x]
        s1=F.sum(inverse_differences)
        s2=F.sum(F.mul(inverse_differences[j],inverse_differences[k])
                 for j in range(len(inverse_differences)) for k in range(j+1,len(inverse_differences)))
        R=F.add(F.mul(F.const(3),F.mul(x,x)),C.a)
        aa=F.neg(F.add(F.div(R,F.mul(F.const(2),y)),F.mul(F.mul(F.const(2),y),s1)))
        bb=F.sub(F.sub(F.sub(F.mul(aa,aa),F.mul(F.const(2),x)),
                        F.mul(F.mul(F.const(2),R),s1)),F.mul(F.mul(F.const(4),F.mul(y,y)),s2))
        a.append(aa);b.append(bb)
    return a,b


def fixture_for_order(n,matching):
    fields=[n] if matching else [p for p in range(5,102) if prime(p) and p!=n and (p+1+2*sp.integer_nthroot(p,2)[0]+2)>=n]
    for p in fields:
        F=Field(p)
        for A in range(p):
            for B in range(p):
                if (4*A**3+27*B*B)%p==0:continue
                C=Curve(F,A,B)
                if C.order%n==0:return C,next(C.subgroups(n))
    raise AssertionError(f'fixture not found for n={n}, matching={matching}')


def check_fixture(C,seq,label):
    F=C.F;n=len(seq);aa,bb=local_coefficients(C,seq)
    u,rat,lam=residue_profile(C,seq,complete=True)
    assert bb[1:]==rat
    invariants=[]
    for i,(x,y) in enumerate(seq[1:],1):
        slope=F.div(F.add(F.mul(F.const(3),F.mul(x,x)),C.a),F.mul(F.const(2),y))
        assert aa[(2*i)%n]==F.add(F.mul(F.const(2),aa[i]),F.mul(F.const(n),slope))
        invariants.append(F.add(F.sub(F.mul(F.const(2),bb[i]),F.mul(aa[i],aa[i])),F.mul(F.const(n),x)))
    assert len(set(invariants))==1
    if n==F.p:assert aa[1]!=0
    if n>=7:assert u is None
    return dict(label=label,field=F.metadata(),A=C.a,B=C.b,subgroup_order=n,
                curve_order=C.order,generator=seq[1],a_coefficients=aa[1:],b_coefficients=bb[1:],
                doubling_checks=n-1,residue_coefficient_checks=n-1,
                invariant_value=invariants[0],lower_degree_exists=u is not None,pole_value=u)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('uniform_probe.json'))
    args=parser.parse_args();started=time.monotonic()
    result=dict(schema='trr07-uniform-exclusion-v1',sympy=sp.__version__,
                certificate=polynomial_certificate(),fixtures=[],
                proof_scope='Written algebraic proof; integer identities and finite calibrations mechanically checked. No Lean formalization of the divisor argument.')
    F=Field(11);C=Curve(F,2,9)
    result['fixtures'].append(check_fixture(C,C.sequence((4,2),5),'known_order_five_exception'))
    for n in [7,11,13,17,19,23,29,31]:
        for matching in [False,True]:
            C,seq=fixture_for_order(n,matching)
            result['fixtures'].append(check_fixture(C,seq,'matching_characteristic' if matching else 'tame'))
    result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [Path(__file__),Path(__file__).with_name('finite_fields.py')]}
    result['total_doubling_checks']=sum(f['doubling_checks'] for f in result['fixtures'])
    result['elapsed_seconds']=round(time.monotonic()-started,6)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(integer_identities=result['certificate']['identity_count'],
                         fixtures=len(result['fixtures']),doubling_checks=result['total_doubling_checks'],
                         elapsed_seconds=result['elapsed_seconds']),sort_keys=True))


if __name__=='__main__':main()
