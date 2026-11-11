"""TOE-11: exact homogeneous highest-derivative Hessian of a declared GfE/YM trial.

This is an algebraic partial-jet audit of the TOE-10 action
 L = (3/2) sum(E_i^2-B_i^2) - 3*sigma*log(D)
 D=(1-alpha*e-2*beta*A)*(1+alpha*b-2*beta*B)+alpha^2*c^2,
 e=sum E_i^2, b=sum B_i^2, c=sum E_i B_i.
A and B are independent FLRW curvature coordinates, with B held fixed when
computing the principal Hessian in (A, E_1, ..., E_n). These are NOT the
full gauge-fixed spacetime metric/G-field/YM principal equations. In the
minisuperspace action A contains ddot(a)/a and E_i contains dot(psi_i).

For sigma>0 and 1-2*beta*B>0 we prove by exact rational arithmetic that
this *jet* Hessian is positive definite wherever T,D>0, including at a
spectral Krein collision. Nondegenerate higher derivatives can still generate
Ostrogradsky or constraint-sector instabilities; positive jet Hessian is not
a claim of stability, strong hyperbolicity, or a tensor propagation cone.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence


def rat(x):
    if type(x) is bool:
        raise ValueError('boolean is not a rational physical input')
    return Q(x)


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),Q())


def det(matrix):
    """Exact Fraction determinant with independent elimination."""
    n=len(matrix)
    if n==0 or any(len(row)!=n for row in matrix):
        raise ValueError('nonempty square matrix required')
    a=[[rat(v) for v in row] for row in matrix]
    result=Q(1)
    for col in range(n):
        pivot=next((k for k in range(col,n) if a[k][col]),None)
        if pivot is None:return Q()
        if pivot!=col:
            a[col],a[pivot]=a[pivot],a[col]
            result=-result
        p=a[col][col]
        result*=p
        for k in range(col+1,n):
            t=a[k][col]/p
            for l in range(col+1,n):a[k][l]-=t*a[col][l]
            a[k][col]=Q()
    return result


def quad(matrix,vector):
    n=len(vector)
    if len(matrix)!=n or any(len(row)!=n for row in matrix):
        raise ValueError('invalid quadratic form')
    return sum((vector[i]*matrix[i][j]*vector[j]
                for i in range(n) for j in range(n)),Q())


@dataclass(frozen=True)
class PartialJet:
    electric: tuple[Q,...]
    magnetic: tuple[Q,...]
    A: Q
    Bcurv: Q
    alpha: Q
    beta: Q
    sigma: Q
    theta_e: Q
    theta_b: Q
    determinant: Q
    discriminant: Q
    base_magnetic: Q
    v: tuple[Q,...]
    gauge_base: tuple[tuple[Q,...],...]
    full_hessian: tuple[tuple[Q,...],...]
    curvature_entry: Q
    mixed_entries: tuple[Q,...]
    gauge_hessian: tuple[tuple[Q,...],...]
    full_determinant: Q
    factorized_determinant: Q

    @property
    def positive_real_spectral(self):
        trace=self.theta_e+self.theta_b
        diagonalizable=self.discriminant!=0 or self.alpha*dot(self.electric,self.magnetic)==0
        return self.discriminant>=0 and diagonalizable and trace>0 and self.determinant>0

    @property
    def proven_positive_jet(self):
        # Sufficient *analytical* conditions of the sum-of-squares certificate.
        return (self.sigma>0 and self.base_magnetic>0 and
                self.theta_b>0 and self.determinant>0 and
                self.curvature_entry>0)

    def squares(self,delta_a,delta_e):
        """Exact completed squares for fluctuations of A and electric fields."""
        da=rat(delta_a); de=tuple(map(rat,delta_e))
        if len(de)!=len(self.electric):raise ValueError('wrong electric variation length')
        first=Q(12)*self.sigma/self.determinant**2 * (
            self.beta*self.theta_b*da+self.alpha*dot(self.v,de))**2
        norm=dot(de,de)
        magnetic_area=dot(self.magnetic,self.magnetic)*norm-dot(self.magnetic,de)**2
        second=3*norm+Q(6)*self.sigma*self.alpha/self.determinant*(
            self.base_magnetic*norm+self.alpha*magnetic_area)
        return first+second


def partial_jet(electric:Sequence,magnetic:Sequence, *, A, Bcurv, alpha, beta, sigma):
    E=tuple(map(rat,electric));B=tuple(map(rat,magnetic))
    if len(E)!=len(B) or len(E)<1:
        raise ValueError('nonempty equal-length electric and magnetic lists required')
    A,Bcurv,alpha,beta,sigma=map(rat,(A,Bcurv,alpha,beta,sigma))
    if alpha<=0 or beta<=0 or sigma<0:raise ValueError('alpha,beta>0 and sigma>=0 required')
    e,b,c=dot(E,E),dot(B,B),dot(E,B)
    S=1-alpha*e-2*beta*A
    T=1+alpha*b-2*beta*Bcurv
    base=1-2*beta*Bcurv
    D=S*T+alpha*alpha*c*c
    if D<=0:raise ValueError('positive log-determinant branch required')
    v=tuple(T*x-alpha*c*y for x,y in zip(E,B))
    n=len(E)
    # Separating the Hessian into a positive rank-one curvature/mixed term
    # and the gauge background Hessian is the exact Schur cancellation.
    K0=tuple(tuple((3 if i==j else 0)
         +6*sigma*alpha/D * (T*(i==j)-alpha*B[i]*B[j])
         for j in range(n)) for i in range(n))
    pref=12*sigma/(D*D)
    p=beta*T
    q=tuple(alpha*x for x in v)
    H=((pref*p*p,)+tuple(pref*p*x for x in q),)+tuple(
      (pref*p*q[i],)+tuple(K0[i][j]+pref*q[i]*q[j] for j in range(n))
      for i in range(n))
    K=tuple(tuple(H[i+1][j+1] for j in range(n)) for i in range(n))
    full=det(H)
    fact=H[0][0]*det(K0)
    assert full==fact
    disc=(S-T)**2-4*alpha*alpha*c*c
    return PartialJet(E,B,A,Bcurv,alpha,beta,sigma,S,T,D,disc,base,v,
                      K0,H,H[0][0],H[0][1:],K,full,fact)


def two_flavor_determinant(checked:PartialJet):
    """Closed product formula for two flavor factors and the curvature jet."""
    if len(checked.electric)!=2:raise ValueError('two gauge multiplets required')
    q=checked
    k_perp=3+6*q.sigma*q.alpha*q.theta_b/q.determinant
    k_parallel=3+6*q.sigma*q.alpha*q.base_magnetic/q.determinant
    predicted=q.curvature_entry*k_perp*k_parallel
    assert predicted==q.full_determinant
    return predicted


def example():
    """Same background and flavor choice as TOE-10 boundary, two sides."""
    a=Q(3,500);beta=Q(1,100);sig=Q(1,100)
    kw=dict(A=Q(2,5),Bcurv=Q(1),alpha=a,beta=beta,sigma=sig)
    out={}
    for name,second in [('real',Q(1001,1000)),('defective',Q(1)),('complex',Q(999,1000))]:
        t=partial_jet((2,second),(1,0),**kw)
        out[name]={'spectral_disc':str(t.discriminant),
                   'positive_real_spectrum':t.positive_real_spectral,
                   'positive_jet':t.proven_positive_jet,
                   'hessian_det':str(t.full_determinant),
                   'mix0':str(t.mixed_entries[0]),
                   'mix1':str(t.mixed_entries[1]),
                   'kinetic_schur_factor':str(two_flavor_determinant(t))}
    return {'schema':'mathcan.toe11.partial_jet.v1',
            'scope':'homogeneous partial-jet Hessian of declared trial action, not full spacetime principal symbol',
            'alpha':str(a),'beta':str(beta),'sigma':str(sig),'A':'2/5','Bcurv':'1',
            'cases':out}

if __name__=='__main__':
    import json
    print(json.dumps(example(),indent=2,sort_keys=True))
