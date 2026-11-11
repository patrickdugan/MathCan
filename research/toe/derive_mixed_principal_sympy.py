"""Optional independent symbolic check of TOE-11 Hessian formulas (needs SymPy)."""
import sympy as sp

A,Bcurv,alpha,beta,sigma=sp.symbols('A B alpha beta sigma', real=True)
E1,E2,B1,B2=sp.symbols('E1 E2 B1 B2', real=True)
E=sp.Matrix([E1,E2]);B=sp.Matrix([B1,B2]);
e=(E.T*E)[0]; b=(B.T*B)[0];c=(E.T*B)[0]
T=1+alpha*b-2*beta*Bcurv
S=1-alpha*e-2*beta*A
D=S*T+alpha**2*c**2
L=sp.Rational(3,2)*(e-b)-3*sigma*sp.log(D)
v=T*E-alpha*c*B
p=beta*T
rank=sp.Matrix([p,alpha*v[0],alpha*v[1]])
K0=3*sp.eye(2)+6*sigma*alpha/D*(T*sp.eye(2)-alpha*(B*B.T))
expected=sp.diag(0,0,0)
for i in range(2):
 for j in range(2):expected[i+1,j+1]=K0[i,j]
expected+=12*sigma/D**2*(rank*rank.T)
actual=sp.hessian(L,[A,E1,E2])
for i in range(3):
 for j in range(3):
  diff=sp.factor(actual[i,j]-expected[i,j])
  assert diff==0,(i,j,diff)
# Independent symbolic identities used by the exact-rational implementation.
assert sp.factor(T-alpha*b-(1-2*beta*Bcurv))==0
print('SymPy: all 9 Hessian entries agree with the rank-one decomposition')
print('Curvature entry:',sp.factor(actual[0,0]))
