"""Optional independent symbolic variation of TOE-08 action (needs SymPy).

Use the coordinate two-form w=B_(23) rather than physical b=w/a² when
varying the spatial metric. N is independent. This avoids erroneous stress
from holding the orthonormal components fixed during metric variation.
"""
import sympy as s

def verify():
    a,N,w,ad,wd,add,wdd,H,Hd,b,v,m2,lam=s.symbols(
        'a N w ad wd add wdd H Hd b v m2 lam', real=True, positive=True)
    L=3*wd**2/(2*N*a)-3*N*m2*w**2/(2*a)+3*lam*ad**2*w**2/(N*a**3)
    rho=s.diff(L,N).subs(N,1)*(-1/a**3)
    rho=s.factor(rho.subs({w:a**2*b,wd:a**2*v,ad:a*H}))
    exp_rho=s.Rational(3,2)*(v**2+m2*b**2)+3*lam*H**2*b**2
    assert s.simplify(rho-exp_rho)==0
    dldt_ad=s.diff(L,ad).subs(N,1)
    tot_dt=s.diff(dldt_ad,a)*ad+s.diff(dldt_ad,w)*wd+s.diff(dldt_ad,ad)*add
    p=(s.diff(L,a).subs(N,1)-tot_dt)/(3*a*a)
    p=s.factor(p.subs({w:a**2*b,wd:a**2*v,ad:a*H,add:a*(Hd+H**2)}))
    exp_p=-v*v/2+m2*b*b/2+3*lam*H**2*b**2-2*lam*(Hd+H**2)*b**2-4*lam*H*b*v
    assert s.simplify(p-exp_p)==0
    # Spatial B Euler equation: d/dt(L_wdot)-L_w=0.
    ld=s.diff(L,wd).subs(N,1)
    dt_ld=s.diff(ld,a)*ad+s.diff(ld,w)*wd+s.diff(ld,wd)*wdd
    eom=s.factor((dt_ld-s.diff(L,w).subs(N,1))/(3*a))
    # wddot/a² = dot(v)+2H v; after expressing q=v=wdot/a².
    vd=s.symbols('vd',real=True)
    eom=s.factor(eom.subs({w:a**2*b,wd:a**2*v,ad:a*H,wdd:a**2*(vd+2*H*v)}))
    assert s.simplify(eom-(vd+H*v+(m2-2*lam*H*H)*b))==0
    print('PASS: 2-form triad lapse/spatial stress and Euler equation')
    return True

if __name__=='__main__':verify()
