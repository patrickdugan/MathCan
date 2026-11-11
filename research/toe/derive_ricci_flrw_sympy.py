import sympy as s
t=s.symbols('t',real=True)
a=s.Function('a')(t);U=s.Function('U')(t);V=s.Function('V')(t)
H=s.diff(a,t)/a
n=4
G=s.diag(-1,a*a,a*a,a*a); GI=s.diag(-1,1/a**2,1/a**2,1/a**2)
gamma={}
for i in (1,2,3):
 gamma[(0,i,i)]=a*s.diff(a,t);gamma[(i,0,i)]=H;gamma[(i,i,0)]=H
def C(u,v,w):return gamma.get((u,v,w),0)
def d(expr,mu):return s.diff(expr,t) if mu==0 else 0
Pl=s.diag(-U,a*a*V,a*a*V,a*a*V)
Pu=s.diag(-U,V/a**2,V/a**2,V/a**2)
Pm=s.zeros(4,4)
for nu in range(n):
 for al in range(n):Pm[nu,al]=sum(Pl[nu,b]*GI[b,al] for b in range(n))
Q={}
for b in range(n):
 for mu in range(n):
  for nu in range(n):
   Q[(b,mu,nu)]=s.expand(d(Pl[mu,nu],b)-sum(C(k,b,mu)*Pl[k,nu]+C(k,b,nu)*Pl[mu,k] for k in range(n)))
T={}
for mu in range(n):
 for nu in range(n):
  for al in range(n):
   T[(mu,nu,al)]=s.expand(d(Pm[nu,al],mu)+sum(C(al,mu,k)*Pm[nu,k]-C(k,mu,nu)*Pm[k,al] for k in range(n)))
K={}
for mu in range(n):
 for nu in range(n):
  K[mu,nu]=s.simplify(sum(d(T[mu,nu,al],al)+sum(C(al,al,k)*T[mu,nu,k]-C(k,al,mu)*T[k,nu,al]-C(k,al,nu)*T[mu,k,al] for k in range(n)) for al in range(n)))
J={}
for al in range(n):
 J[al]=s.simplify(sum(d(Pu[al,b],b)+sum(C(al,b,k)*Pu[k,b]+C(b,b,k)*Pu[al,k] for k in range(n)) for b in range(n)))
S=s.simplify(sum(d(J[al],al)+sum(C(al,al,k)*J[k] for k in range(n)) for al in range(n)))
box={}
for mu in range(n):
 for nu in range(n):
  box[mu,nu]=s.simplify(sum(GI[al,b]*(d(Q[b,mu,nu],al)-sum(C(k,al,b)*Q[k,mu,nu]+C(k,al,mu)*Q[b,k,nu]+C(k,al,nu)*Q[b,mu,k] for k in range(n))) for al in range(n) for b in range(n)))
D={}
for mu,nu in ((0,0),(1,1)):
 D[mu,nu]=s.simplify((G[mu,nu]*S+box[mu,nu]-K[mu,nu]-K[nu,mu])/2)
print('J0',s.simplify(J[0]))
print('S',s.collect(s.expand(S),[s.diff(U,t,2),s.diff(V,t,2),s.diff(U,t),s.diff(V,t)]))
for mu,nu in ((0,0),(1,1)):
 print('K',mu,nu,s.simplify(K[mu,nu]/(a*a if mu else 1)))
 print('Box',mu,nu,s.simplify(box[mu,nu]/(a*a if mu else 1)))
 print('D',mu,nu,s.simplify(D[mu,nu]/(a*a if mu else 1)))
D00=s.simplify(D[0,0]);Ds=s.simplify(D[1,1]/a**2)
for name,expr in [('D00',D00),('Ds',Ds)]:
  sub=s.simplify(expr.subs(V,U).doit())
  print('common',name,sub)
