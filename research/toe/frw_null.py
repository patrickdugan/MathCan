"""Exact rational Friedmann polynomial null-space checks (synthetic inputs)."""
from fractions import Fraction as F
from .graph_entropy import q, quotient_action, matvec, kernel, transpose


def frw_design(redshifts):
    if not redshifts:raise ValueError("no redshifts")
    values=list(map(q,redshifts))
    if any(z<0 for z in values):raise ValueError("redshifts must be nonnegative")
    return [[F(1),(1+z)**2,(1+z)**3,(1+z)**4] for z in values]


def frw_signal(redshifts,params):
    """Conventional E(z)^2; params=(Lambda,curvature,matter,radiation)."""
    if len(params)!=4:raise ValueError("four nuisance parameters")
    return matvec(frw_design(redshifts),list(map(q,params)))


def frw_obstruction(redshifts,observed,variances):
    design=frw_design(redshifts);n=len(design)
    if len(observed)!=n or len(variances)!=n:raise ValueError("shape mismatch")
    if any(q(v)<=0 for v in variances):raise ValueError("positive variances")
    cov=[[q(variances[i]) if i==j else F(0) for j in range(n)] for i in range(n)]
    return quotient_action(observed,design,cov)


def frw_null_relations(redshifts):
    a=frw_design(redshifts)
    return kernel(transpose(a),len(redshifts))
