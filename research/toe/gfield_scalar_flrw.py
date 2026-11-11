"""TOE-05: flat FLRW homogeneous REAL SCALAR reduction of Lambda-GfE.

Bianconi arxiv:2610.34496, equations (5),(7),(9),(16),(31),(45)-(49).
We impose scalar-field homogeneity and spatial flatness on the induced-metric
logarithmic action and take the metric-equivalent volume multiplier variation.
This is a symmetry-reduced action calculation. It is NOT yet a verified
componentwise reduction of the full covariant dressed T and D tensors.

All results are dimensionless, synthetic, and restricted to beta>0, alpha>0,
H>0 and positive induced metric eigenvalues. Alpha = 6*kappa*beta in GR limit.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
import math


class DomainError(ValueError):
    """Outside the strictly positive induced-metric, expanding, finite domain."""


SECTORS = ("scalar", "timelike_vector", "spacelike_vector",
           "timelike_bivector", "spacelike_bivector")
WEIGHTS = (1, 1, 3, 3, 3)


def _scalar(x, label):
    if type(x) not in (int, float, Fraction) or not math.isfinite(float(x)):
        raise ValueError(f"{label} must be finite")
    return float(x)


@dataclass(frozen=True)
class ScalarModel:
    beta: float
    alpha: float
    mass: float
    Lambda: float

    def __post_init__(self):
        for n in ("beta", "alpha", "mass", "Lambda"):
            x = _scalar(getattr(self, n), n)
            if (n in ("beta", "alpha") and x <= 0) or (n == "mass" and x < 0):
                raise ValueError("alpha and beta must be positive; mass nonnegative")
            object.__setattr__(self, n, x)

    @property
    def kappa(self):
        return self.alpha / (6 * self.beta)

    def spectral(self, H, q, phi, pi):
        """Five theta=1+alpha*M-beta*R eigenvalues, multiplicity (1,1,3,3,3)."""
        H,q,phi,pi = (_scalar(v,n) for v,n in zip((H,q,phi,pi),
                                   ("H", "Hdot", "phi", "phidot")))
        A = H*H + q
        B = H*H
        a,b,m2 = self.alpha,self.beta,self.mass**2
        ds = (1+a*m2*phi*phi-6*b*(A+B),
              1-a*pi*pi-3*b*A,
              1-b*(A+2*B),
              1-2*b*A,
              1-2*b*B)
        if any(not math.isfinite(d) or d <= 0 for d in ds):
            raise DomainError("G-field induced-metric eigenvalue lost positivity")
        return ds

    def partials(self,H,q,phi,pi):
        ds=self.spectral(H,q,phi,pi)
        d0,d1,d2,d3,d4=ds
        a,b,m2=self.alpha,self.beta,self.mass**2
        f=-math.fsum(w*math.log(d) for w,d in zip(WEIGHTS,ds))
        fa=6*b/d0+3*b/d1+3*b/d2+6*b/d3
        fb=6*b/d0+6*b/d2+6*b/d4
        fphi=-2*a*m2*phi/d0
        fpi=2*a*pi/d1
        faa=36*b*b/(d0*d0)+9*b*b/(d1*d1)+3*b*b/(d2*d2)+12*b*b/(d3*d3)
        fab=36*b*b/(d0*d0)+6*b*b/(d2*d2)
        faphi=-12*a*b*m2*phi/(d0*d0)
        fapi=6*a*b*pi/(d1*d1)
        fpipi=2*a/d1+4*a*a*pi*pi/(d1*d1)
        return {"f":f,"fa":fa,"fb":fb,"fphi":fphi,"fpi":fpi,
                "faa":faa,"fab":fab,"faphi":faphi,"fapi":fapi,
                "fpipi":fpipi,"theta":ds}

    def determinant_certificate(self,H,q,phi,pi):
        """Exact float identity: Schur determinant = positive base + positive extra.

        f_AA f_pi,pi - f_A,pi**2
          = (2 alpha/theta_t) f_AA +
            (4 alpha**2 pi**2/theta_t**2)*(f_AA - 9 beta**2/theta_t**2).
        """
        p=self.partials(H,q,phi,pi)
        d1=p["theta"][1]
        core=p["faa"]-9*self.beta**2/d1**2
        decomposition=(2*self.alpha/d1)*p["faa"] + (
            4*self.alpha**2*pi*pi/d1**2)*core
        direct=p["faa"]*p["fpipi"]-p["fapi"]**2
        return {"direct":direct,"decomposed":decomposition,
                "orthogonal_curvature":core,"positive":direct>0 and core>0}

    def rhs(self,H,q,phi,pi):
        """Return (dH, dHdot, dphi, dphidot) by solving lapse + scalar EL.

        The lapse constraint is linear in Hddot, phiddot after expanding d(f_A)/dt.
        The scalar Euler-Lagrange equation is d(f_pi)/dt +3H f_pi-f_phi=0.
        """
        H,q,phi,pi=(_scalar(v,n) for v,n in zip((H,q,phi,pi),
                                   ("H","Hdot","phi","phidot")))
        if H<=0:raise DomainError("expanding branch H>0 required")
        p=self.partials(H,q,phi,pi)
        faa,fapi,fpipi=p["faa"],p["fapi"],p["fpipi"]
        det=H*(faa*fpipi-fapi*fapi)
        if det<=0:raise DomainError("singular coupled matter-curvature evolution")
        const=p["f"]-6*self.beta*self.Lambda+(H*H-q)*p["fa"] - 2*H*H*p["fb"]-pi*p["fpi"] +H*(2*H*q*(faa+p["fab"])+p["faphi"]*pi)
        second=2*H*q*fapi+3*H*p["fpi"]-p["fphi"]
        b1,b2=-const,-second
        j=(b1*fpipi-H*fapi*b2)/det
        pidot=(H*faa*b2-fapi*b1)/det
        if not (math.isfinite(j) and math.isfinite(pidot)):
            raise DomainError("non-finite time derivatives")
        return (q,j,pi,pidot)

    def residuals(self,H,q,phi,pi,j,pidot):
        p=self.partials(H,q,phi,pi)
        dA=j+2*H*q
        dB=2*H*q
        fa_dot=p["faa"]*dA+p["fab"]*dB+p["faphi"]*pi+p["fapi"]*pidot
        pi_dot=p["fapi"]*dA+p["fpipi"]*pidot
        lapse=p["f"]-6*self.beta*self.Lambda+(H*H-q)*p["fa"]-2*H*H*p["fb"]-pi*p["fpi"]+H*fa_dot
        scalar=pi_dot+3*H*p["fpi"]-p["fphi"]
        return (lapse,scalar)

    def scalar_bare_exchange(self,H,q,phi,pi,j,pidot):
        """Exact on-shell identity for the conventional bare-scalar diagnostic.

        rho_bare=pi²+m² phi², p_bare=pi²-m² phi².
        This is distinct from the dressed stress tensor defined by metric variation.
        """
        d0,d1,_,_,_=self.spectral(H,q,phi,pi)
        theta_t_dot=-2*self.alpha*pi*pidot-3*self.beta*(j+2*H*q)
        bare=2*pi*(pidot+3*H*pi+self.mass**2*phi)
        inferred=2*pi*(pi*theta_t_dot/d1+self.mass**2*phi*(1-d1/d0))
        return bare,inferred

    def lambda_for_initial_acceleration(self,H,q,phi,pi,j):
        """Calibrate Lambda to the lapse at one state with chosen Hddot j.

        d(pi)/dt is supplied by the scalar Euler-Lagrange equation at fixed j.
        This creates consistent initial data; no observational calibration implied.
        """
        p=self.partials(H,q,phi,pi)
        pidot=-(p["fapi"]*(j+2*H*q)+3*H*p["fpi"]-p["fphi"])/p["fpipi"]
        fa_dot=p["faa"]*(j+2*H*q)+p["fab"]*(2*H*q)+p["faphi"]*pi+p["fapi"]*pidot
        lam=(p["f"]+(H*H-q)*p["fa"]-2*H*H*p["fb"]-pi*p["fpi"]+H*fa_dot)/(6*self.beta)
        return lam,pidot

    def evolve(self, redshifts, *, H0, Hdot0, phi0, pi0, max_step=0.001):
        """RK4 in redshift; synthetic curve with full 4D scalar/metric reduced flow."""
        zz=tuple(_scalar(z,"redshift") for z in redshifts)
        if not zz or zz[0]!=0 or any(x<0 for x in zz) or any(a>=b for a,b in zip(zz,zz[1:])):
            raise ValueError("redshifts must begin at 0 and increase strictly")
        if _scalar(max_step,"max_step")<=0: raise ValueError("positive max step required")
        state=tuple(float(x) for x in (H0,Hdot0,phi0,pi0))
        def derivative(z,s):
            H,q,phi,pi=s
            dt=self.rhs(H,q,phi,pi)
            return tuple(-v/((1+z)*H) for v in dt)
        out=[];z=0.
        for target in zz:
            if target>z:
                steps=math.ceil((target-z)/max_step)
                dz=(target-z)/steps
                for _ in range(steps):
                    k1=derivative(z,state)
                    k2=derivative(z+dz/2,tuple(v+dz*w/2 for v,w in zip(state,k1)))
                    k3=derivative(z+dz/2,tuple(v+dz*w/2 for v,w in zip(state,k2)))
                    k4=derivative(z+dz,tuple(v+dz*w for v,w in zip(state,k3)))
                    state=tuple(v+dz*(a+2*b+2*c+d)/6 for v,a,b,c,d in zip(state,k1,k2,k3,k4))
                    z+=dz
                z=target
            H,q,phi,pi=state
            _,j,_,pd=self.rhs(*state)
            lapse,el=self.residuals(H,q,phi,pi,j,pd)
            out.append({"z":target,"H":H,"Hdot":q,"phi":phi,"phidot":pi,
                        "Hddot":j,"phiddot":pd,"G":tuple(1/d for d in self.spectral(*state)),
                        "constraint_residual":lapse,"scalar_residual":el,
                        "bare_exchange":self.scalar_bare_exchange(H,q,phi,pi,j,pd)[0]})
        return tuple(out)


def rational_determinant(beta,alpha,mass2,A,B,phi,pi):
    """Exact rational Schur certificate on a rational induced-metric state."""
    b,a,m=map(Fraction,(beta,alpha,mass2))
    A,B,phi,pi=map(Fraction,(A,B,phi,pi))
    if not (a>0 and b>0 and m>=0):raise ValueError("positive couplings required")
    d0=1+a*m*phi*phi-6*b*(A+B)
    d1=1-a*pi*pi-3*b*A
    d2=1-b*(A+2*B)
    d3=1-2*b*A
    d4=1-2*b*B
    if min(d0,d1,d2,d3,d4)<=0:raise DomainError("invalid rational G-field")
    faa=36*b*b/d0**2+9*b*b/d1**2+3*b*b/d2**2+12*b*b/d3**2
    fapi=6*a*b*pi/d1**2
    fpipi=2*a/d1+4*a*a*pi*pi/d1**2
    peripheral=faa-9*b*b/d1**2
    det=faa*fpipi-fapi*fapi
    decomposed=(2*a/d1)*faa + (4*a*a*pi*pi/d1**2)*peripheral
    assert det==decomposed
    assert det>0 and peripheral>0
    return {"theta":(d0,d1,d2,d3,d4),"direct":det,
            "decomposed":decomposed,"peripheral":peripheral}


def tracefree_flrw(geo_temporal,geo_spatial,rho,p,kappa):
    """Source eq(47): X00+Xs=3*kappa*(rho+p), residual.

    X=R_G(symmetric)+D(symmetric); rho,p are DRESSED matter values.
    Independent of beta and the chosen scalar truncation.
    """
    return (geo_temporal+geo_spatial)-3*kappa*(rho+p)


def reference_experiment():
    import json
    H,q,phi,pi=1.0,-0.01,0.2,-0.1
    base=ScalarModel(beta=.01,alpha=.06,mass=.4,Lambda=0)
    # The initial jerk is chosen at its leading-order GR value, then Lambda
    # is calibrated using the full nonlinear initial lapse and matter equation.
    kgdot=-3*H*pi-base.mass**2*phi
    j=-2*base.kappa*pi*kgdot
    lam,_=base.lambda_for_initial_acceleration(H,q,phi,pi,j)
    model=ScalarModel(beta=.01,alpha=.06,mass=.4,Lambda=lam)
    zz=(0,.1,.2,.3,.4,.5)
    curve=model.evolve(zz,H0=H,Hdot0=q,phi0=phi,pi0=pi,max_step=.0004)
    return {"schema":"mathcan.toe05.scalar.v1","sources":
            ["arxiv:2610.34496 eqs 5,7,9,31,46-48", "arxiv:2510.22545 secs III-IV"],
            "scope":"homogeneous real scalar; flat expanding branch; on-shell G-field; synthetic",
            "beta":model.beta,"alpha":model.alpha,"mass":model.mass,
            "Lambda":lam,"kappa":model.kappa,"initial":{
                "H":H,"Hdot":q,"phi":phi,"phidot":pi,"Hddot":j},
            "redshifts":list(zz),"curve":[{k:(round(v,12) if isinstance(v,float) else v)
                  for k,v in row.items() if k!="G"} | {"G_min":round(min(row["G"]),12)}
                  for row in curve],
            "max_lapse_residual":max(abs(x["constraint_residual"]) for x in curve),
            "max_scalar_residual":max(abs(x["scalar_residual"]) for x in curve),
            "evidence":"symmetry-reduced model, not full tensor-component verification or observations"}


if __name__=="__main__":
    import json
    print(json.dumps(reference_experiment(),indent=2,sort_keys=True))
