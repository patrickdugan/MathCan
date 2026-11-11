"""Optional independent SymPy check of TOE-10's declared logarithmic medium.

Only the homogeneous prescribed-metric matter action is varied. This script
is not part of standard-library CI and does not claim the full GfE equations.
"""
import sympy as s
E1,E2,B1,B2,H,Hdot,alpha,beta,sigma=s.symbols(
    'E1 E2 B1 B2 H Hdot alpha beta sigma',real=True)
E=[E1,E2];B=[B1,B2]
e=E1**2+E2**2
b=B1**2+B2**2
c=E1*B1+E2*B2
te=1-alpha*e-2*beta*(H**2+Hdot)
tb=1+alpha*b-2*beta*H**2
D=te*tb+alpha**2*c**2
L=s.Rational(3,2)*(e-b)-3*sigma*s.log(D)
P=[3*E[i]+6*sigma*alpha*(tb*E[i]-alpha*c*B[i])/D for i in range(2)]
Q=[-3*B[i]-6*sigma*alpha*(te*B[i]+alpha*c*E[i])/D for i in range(2)]
for i in range(2):
    assert s.simplify(s.diff(L,E[i])-P[i])==0
    assert s.simplify(s.diff(L,B[i])-Q[i])==0
for i in range(2):
    for j in range(2):
        assert s.simplify(s.diff(P[i],E[j])-s.diff(P[j],E[i]))==0
        assert s.simplify(s.diff(P[i],B[j])-s.diff(Q[j],E[i]))==0
print('TOE-10 independent scalar variational derivatives and mixed Hessians: PASS')
