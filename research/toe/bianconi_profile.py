"""TOE-03: exact-rational, covariance-aware tests for an assumed FRW H(z) proxy.

This module does NOT solve Bianconi's full ΛGfE field equations. It profiles
an explicitly specified E(z)^2 perturbation against the four ordinary FRW
background columns using exact rational arithmetic and a disclosed synthetic
covariance. No cosmological dataset or posterior is claimed.
"""
from __future__ import annotations

from fractions import Fraction as F
from math import sqrt


def rational(value):
    if isinstance(value, float) or isinstance(value, bool):
        raise TypeError("use exact integer, Fraction or decimal string inputs")
    return F(value)


def redshift_grid(redshifts):
    z = tuple(rational(t) for t in redshifts)
    if not z or any(t < 0 for t in z) or len(set(z)) != len(z):
        raise ValueError("need distinct nonnegative redshifts")
    return z


def frw_design(redshifts):
    return tuple((F(1), (1+z)**2, (1+z)**3, (1+z)**4)
                 for z in redshift_grid(redshifts))


def dot(a, b):
    if len(a) != len(b):
        raise ValueError("vector shape mismatch")
    return sum((x*y for x,y in zip(a,b)), F(0))


def matvec(matrix, vector):
    return tuple(dot(row, vector) for row in matrix)


def transpose(matrix):
    if not matrix:
        raise ValueError("empty matrix")
    m = len(matrix[0])
    if any(len(row) != m for row in matrix):
        raise ValueError("ragged matrix")
    return tuple(tuple(row[i] for row in matrix) for i in range(m))


def solve(matrix, vector):
    """Dense exact Gaussian elimination with row pivoting and rank checking."""
    n = len(vector)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("square matrix required")
    a = [[rational(x) for x in row]+[rational(y)]
         for row,y in zip(matrix,vector)]
    for j in range(n):
        pivot = next((i for i in range(j,n) if a[i][j]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        a[j],a[pivot] = a[pivot],a[j]
        div = a[j][j]
        a[j][j:] = [v/div for v in a[j][j:]]
        for i in range(n):
            if i==j: continue
            c = a[i][j]
            if c:
                a[i][j:] = [x-c*y for x,y in zip(a[i][j:],a[j][j:])]
    return tuple(a[i][-1] for i in range(n))


def det(matrix):
    """Exact determinant, including rectangular-input rejection."""
    n = len(matrix)
    if any(len(row)!=n for row in matrix):
        raise ValueError("square matrix required")
    a = [[rational(x) for x in row] for row in matrix]
    value=F(1)
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:return F(0)
        if pivot!=j:
            a[j],a[pivot]=a[pivot],a[j]
            value=-value
        x=a[j][j];value*=x
        for i in range(j+1,n):
            coef=a[i][j]/x
            for k in range(j+1,n):
                a[i][k]-=coef*a[j][k]
            a[i][j]=0
    return value


def check_spd(matrix):
    """Exact LDL^T test for strictly positive-definite symmetric covariance."""
    n=len(matrix)
    if n==0 or any(len(row)!=n for row in matrix):
        raise ValueError("nonempty square covariance required")
    a=tuple(tuple(rational(x) for x in row) for row in matrix)
    if any(a[i][j]!=a[j][i] for i in range(n) for j in range(i)):
        raise ValueError("covariance must be symmetric")
    lower=[[F(0)]*n for _ in range(n)]
    diag=[]
    for i in range(n):
        value=a[i][i]-sum((lower[i][k]**2*diag[k] for k in range(i)),F(0))
        if value<=0:raise ValueError("covariance must be positive definite")
        diag.append(value)
        lower[i][i]=F(1)
        for j in range(i+1,n):
            lower[j][i]=(a[j][i]-sum((lower[j][k]*lower[i][k]*diag[k]
                                          for k in range(i)),F(0)))/value
    return a


def synthetic_covariance(redshifts, *, sigma0=F(1,25),
                         sigma_slope=F(1,100), rho=F(1,2),
                         calibration=F(1,50), mode="constant"):
    """Documented *synthetic* E(z)^2 covariance, no observed measurements.

    C_ij = s_i s_j rho^abs(i-j) + tau^2 b_i b_j,
    s_i=sigma0+sigma_slope*z_i, b_i in {1,(1+z_i)^2}.
    AR(1) Toeplitz kernel is SPD when 0<=rho<1; rank-one term is PSD.
    """
    z=redshift_grid(redshifts)
    sigma0,sigma_slope,rho,calibration=map(rational,
                               (sigma0,sigma_slope,rho,calibration))
    if sigma0<=0 or sigma_slope<0 or not 0<=rho<1 or calibration<0:
        raise ValueError("invalid covariance parameters")
    if mode not in ("constant","curvature"):
        raise ValueError("calibration mode must be an FRW nuisance column")
    b=tuple(F(1) if mode=="constant" else (1+x)**2 for x in z)
    sig=tuple(sigma0+sigma_slope*x for x in z)
    c=tuple(tuple(sig[i]*sig[j]*rho**abs(i-j)+calibration**2*b[i]*b[j]
                  for j in range(len(z))) for i in range(len(z)))
    check_spd(c)
    return c


def frw_background(redshifts, omega):
    """Normalized or unnormalized Lambda, curvature, matter, radiation coefficients."""
    if len(omega)!=4:raise ValueError("need exactly four FRW coefficients")
    return matvec(frw_design(redshifts),tuple(map(rational,omega)))


def dynamic_template(redshifts, power):
    """Assumed phenomenological mode f_p=(1+z)^p-1, anchored at z=0."""
    if type(power) is not int or power<0:
        raise ValueError("nonnegative integer template power required")
    return tuple((1+z)**power-1 for z in redshift_grid(redshifts))


def proxy_expansion_squared(redshifts, omega, amplitude, power):
    """E^2(z) proxy, not a solution of Bianconi's modified field equations."""
    base=frw_background(redshifts,omega)
    f=dynamic_template(redshifts,power)
    eps=rational(amplitude)
    result=tuple(a+eps*b for a,b in zip(base,f))
    if any(x<=0 for x in result):
        raise ValueError("nonpositive E(z)^2: invalid expansion proxy")
    return result


def proxy_expansion_hubble(redshifts, omega, amplitude, power, h0):
    """Numerical H(z)=H0 sqrt(E^2) from the stated proxy and positive H0."""
    h0=rational(h0)
    if h0<=0:raise ValueError("positive H0 required")
    return tuple(float(h0)*sqrt(float(y)) for y in
                 proxy_expansion_squared(redshifts,omega,amplitude,power))


def profile(y, design, covariance):
    """Weighted least-squares nuisance profile and exact chi-square residual."""
    b=tuple(tuple(map(rational,row)) for row in design)
    n=len(b)
    if n<4 or any(len(row)!=4 for row in b):
        raise ValueError("design needs at least four rows and four columns")
    if len(y)!=n:raise ValueError("measurement length mismatch")
    c=check_spd(covariance)
    if len(c)!=n:raise ValueError("covariance length mismatch")
    y=tuple(map(rational,y))
    bt=transpose(b)
    weighted_y=solve(c,y)
    weighted_cols=[solve(c,col) for col in bt]
    gram=tuple(tuple(dot(bt[i],weighted_cols[j]) for j in range(4)) for i in range(4))
    rhs=tuple(dot(col,weighted_y) for col in bt)
    nuisance=solve(gram,rhs)
    residual=tuple(yi-fi for yi,fi in zip(y,matvec(b,nuisance)))
    chi2=dot(residual,solve(c,residual))
    return {"nuisance":nuisance,"residual":residual,"chi2":chi2,
            "information":chi2,"gram":gram}


def profile_template(redshifts, covariance, power):
    """Fisher information after profiling the four ordinary FRW parameters."""
    f=dynamic_template(redshifts,power)
    return profile(f,frw_design(redshifts),covariance)


def schur_information(redshifts,covariance,power):
    """Independent Schur-complement calculation using the augmented Gram determinant."""
    b=frw_design(redshifts)
    f=dynamic_template(redshifts,power)
    cols=transpose(tuple(row+(fi,) for row,fi in zip(b,f)))
    c=check_spd(covariance)
    wc=[solve(c,col) for col in cols]
    gram=tuple(tuple(dot(cols[i],wc[j]) for j in range(len(cols)))
                         for i in range(len(cols)))
    base=tuple(tuple(gram[i][j] for j in range(4)) for i in range(4))
    d=det(base)
    if d==0:raise ValueError("FRW nuisance design rank deficient")
    return det(gram)/d


def injection_case(redshifts,covariance,omega,amplitude,power):
    """Noiseless synthetic injection; reports profile chi-square, not a data fit."""
    y=proxy_expansion_squared(redshifts,omega,amplitude,power)
    fit=profile(y,frw_design(redshifts),covariance)
    info=profile_template(redshifts,covariance,power)["chi2"]
    eps=rational(amplitude)
    if fit["chi2"]!=eps*eps*info:
        raise AssertionError("projection quadratic law failed")
    return {"chi2":fit["chi2"],"fisher":info,"eps":eps,
            "unit_amplitude_sigma":(1/sqrt(float(info)) if info else float("inf")),
            "snr":abs(float(eps))*sqrt(float(info)),"fit":fit}


def fraction_string(x):
    f=rational(x)
    return str(f.numerator) if f.denominator==1 else f"{f.numerator}/{f.denominator}"


def reference_experiment():
    """Machine-readable, entirely reproducible *synthetic* covariance example."""
    z=tuple(F(i,5) for i in range(7))
    omega=(F(68,100),F(0),F(32,100),F(0))
    amplitude=F(1,1000)
    params={"sigma0":"1/25","sigma_slope":"1/100","rho":"1/2",
            "calibration":"1/50","mode":"constant"}
    cov=synthetic_covariance(z)
    fit=injection_case(z,cov,omega,amplitude,5)
    return {
        "schema":"mathcan.toe03.synthetic.v1",
        "data_status":"synthetic illustrative E^2; no observational constraint",
        "primary_source":"https://doi.org/10.1016/j.physletb.2026.141014",
        "phenomenological_closure":"E^2=Omega_L+Omega_k*x^2+Omega_m*x^3+Omega_r*x^4+epsilon*(x^p-1); x=1+z",
        "redshifts":[fraction_string(x) for x in z],
        "omega_L_k_m_r":[fraction_string(x) for x in omega],
        "amplitude":fraction_string(amplitude),"power":5,
        "covariance_model":params,
        "covariance_E2":[[fraction_string(x) for x in row] for row in cov],
        "projections":{"p2":fraction_string(profile_template(z,cov,2)["chi2"]),
                       "p3":fraction_string(profile_template(z,cov,3)["chi2"]),
                       "p4":fraction_string(profile_template(z,cov,4)["chi2"]),
                       "p5":fraction_string(fit["fisher"])},
        "injected_chi2":fraction_string(fit["chi2"]),
        "unit_amplitude_sigma":fit["unit_amplitude_sigma"],
        "synthetic_snr":fit["snr"]
    }


if __name__=="__main__":
    import json
    print(json.dumps(reference_experiment(),indent=2))


def gfield_mode(redshifts, *, power=2, order=2):
    """Conditional FRW G-eigenvalue ansatz: (x^power-1)^order.

    If G_k(x)=1+g_k(x^power-1), its exact GfE entropy contribution is
    G_k-1-ln(G_k), with leading quadratic shape g_k^2/2*(x^power-1)^2.
    Neither this ansatz nor additive coupling to E^2 follows from GfE.
    """
    if type(power) is not int or power<1 or type(order) is not int or order<2:
        raise ValueError("positive integer power and order >=2 required")
    return tuple(((1+z)**power-1)**order for z in redshift_grid(redshifts))


def gfield_entropy_series(redshifts, coupling, *, power=2, cutoff=7):
    """Exact-rational alternating-series bracket for u-ln(1+u).

    Valid for 0<=u<1 at every sample, with u=g*((1+z)^power-1).
    Tail absolute bound at each redshift is u^(N+1)/(N+1).
    The GfE thermodynamic term multiplies this shape by z_k/(2*beta).
    """
    g=rational(coupling)
    if g<0 or type(cutoff) is not int or cutoff<2:
        raise ValueError("positive coupling and integer cutoff >=2 required")
    values=[]
    for h in dynamic_template(redshifts,power):
        u=g*h
        if u>=1:raise ValueError("series domain requires u<1")
        partial=sum(((-1)**j*u**j/F(j) for j in range(2,cutoff+1)),F(0))
        error=u**(cutoff+1)/F(cutoff+1)
        values.append((partial,error))
    return tuple(values)
