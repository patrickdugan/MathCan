"""ROC-01 pure-Python reference observer card.

State-local algebra only. H is built from declared future-output Jacobians.
No pretrained checkpoint, decoder fit, or scientific claim is implied.
"""
from __future__ import annotations

from hashlib import sha256
from math import fsum, isfinite, sqrt
from random import Random
from statistics import median
from typing import Sequence

TOL = 1e-8
ZERO, LARGE, HIGH_S, LOW_S = .05, .20, .80, .20
NULL_SEEDS = tuple(range(941001, 941129))


def shape(X):
    if not X or not X[0] or any(len(row) != len(X[0]) for row in X):
        raise ValueError("Nonempty rectangular matrix required")
    if any(not isfinite(float(v)) for row in X for v in row):
        raise ValueError("Nonfinite matrix entry")
    return len(X), len(X[0])


def transpose(X):
    return [list(row) for row in zip(*X)]


def dot(a, b):
    return fsum(x*y for x, y in zip(a, b))


def matmul(A, B):
    n, m = shape(A)
    q, p = shape(B)
    if m != q:
        raise ValueError("Matrix dimensions disagree")
    bt = transpose(B)
    return [[dot(row, col) for col in bt] for row in A]


def frob(A):
    return sqrt(fsum(x*x for row in A for x in row))


def mgs(vectors, tol=TOL):
    basis = []
    for v in vectors:
        w = [float(x) for x in v]
        for _ in range(2):
            for q in basis:
                a = dot(w, q)
                w = [x-a*y for x, y in zip(w, q)]
        length = sqrt(dot(w, w))
        if length > tol:
            basis.append([x/length for x in w])
    return basis


def complement(U, tol=TOL):
    d, k = shape(U)
    if k > d:
        raise ValueError("Observer rank exceeds state dimension")
    cols = transpose(U)
    for i, x in enumerate(cols):
        for j, y in enumerate(cols):
            if abs(dot(x, y)-(1.0 if i==j else 0.0))>tol:
                raise ValueError("U must have orthonormal columns")
    q = []
    for i in range(d):
        v = [float(i==j) for j in range(d)]
        for _ in range(2):
            for col in cols+q:
                a=dot(v,col)
                v=[x-a*y for x,y in zip(v,col)]
        length=sqrt(dot(v,v))
        if length>tol:
            q.append([x/length for x in v])
        if len(q)==d-k:
            break
    if len(q)!=d-k:
        raise AssertionError("Complement construction lost rank")
    return transpose(q) if q else [[] for _ in range(d)]


def causal_gram(jacobians, weights=None):
    if not jacobians:
        raise ValueError("At least one output Jacobian required")
    d=shape(jacobians[0])[1]
    if any(shape(j)[1]!=d for j in jacobians):
        raise ValueError("Jacobian state widths must match")
    if weights is None:
        weights=[1/len(jacobians)]*len(jacobians)
    if (len(weights)!=len(jacobians) or
        any(w<=0 or not isfinite(w) for w in weights) or
        abs(fsum(weights)-1)>1e-8):
        raise ValueError("Positive Jacobian weights must sum to one")
    H=[[0.]*d for _ in range(d)]
    for J,weight in zip(jacobians,weights):
        for row in J:
            for i in range(d):
                for j in range(d):
                    H[i][j]+=weight*row[i]*row[j]
    return H


def projected_norm(D,left,right):
    if not left or not left[0] or not right or not right[0]:
        return 0.
    return frob(matmul(matmul(transpose(left), D), right))


def legacy_labels(a,b,c,s):
    tags=[]
    if b<=ZERO: tags.append("closed_quotient")
    if c<=ZERO: tags.append("invariant_subspace")
    if a<=ZERO and b<=ZERO and s is not None and s>=HIGH_S:
        tags.append("latched_memory")
    if a<=ZERO and b<=ZERO and s is not None and s<=LOW_S:
        tags.append("irrelevant")
    if b>=LARGE and a<=ZERO and c<=ZERO:
        tags.append("output_register")
    return tags or ["unclassified"]


def score_state(T,U,jacobians,*,task_mse=None,weights=None,meta=None):
    d,m=shape(T)
    if d!=m or shape(U)[0]!=d:
        raise ValueError("Square T and d×k U required")
    k=shape(U)[1]
    Q=complement(U)
    D=[[float(T[i][j])-(1. if i==j else 0.)
        for j in range(d)] for i in range(d)]
    H=causal_gram(jacobians,weights)
    if shape(H)!=(d,d):
        raise ValueError("Output Jacobian state width mismatch")
    Dnorm=frob(D)
    A=projected_norm(D,U,U)
    B=projected_norm(D,U,Q)
    C=projected_norm(D,Q,U)
    trH=fsum(H[i][i] for i in range(d))
    captured=fsum(dot(col,[dot(H[i],col) for i in range(d)])
                  for col in transpose(U))
    s=max(0.,min(1.,captured/trH)) if trH>1e-14 else None
    a,b,c=(A/Dnorm,B/Dnorm,C/Dnorm) if Dnorm>1e-14 else (0.,0.,0.)
    if task_mse is not None and (task_mse<0 or not isfinite(task_mse)):
        raise ValueError("Invalid task MSE")
    return {"d":d,"k":k,"A_frob":A,"B_frob":B,"C_frob":C,
            "D_frob":Dnorm,"A_normalized":a,"B_normalized":b,
            "C_normalized":c,"A_per_observed":A/sqrt(k),
            "B_per_observed":B/sqrt(k),"C_per_observed":C/sqrt(k),
            "s_causal":s,"H_trace":trH,"zero_dynamics":Dnorm<=1e-14,
            "task_mse":task_mse,"task_mse_available":task_mse is not None,
            "tags":["unclassified"],
            "tag_status":"null_calibration_required",
            "legacy_absolute_threshold_tags":legacy_labels(a,b,c,s),
            "meta":meta or {}}


def random_basis(d,k,seed):
    if not 1<=k<=d:
        raise ValueError("Invalid observer rank")
    rng=Random(seed)
    cols=[]
    for _ in range(k):
        for _try in range(100):
            updated=mgs(cols+[[rng.gauss(0,1) for _ in range(d)]])
            if len(updated)>len(cols):
                cols=updated
                break
        else:
            raise RuntimeError("Random orthonormalization failed")
    return transpose(cols)


def null_distribution(T,U,jacobians,*,state_key,checkpoint_sha,
                      seeds=NULL_SEEDS):
    d,k=shape(U)
    if len(seeds)<100 or len(set(seeds))!=len(seeds):
        raise ValueError("At least 100 distinct registered seeds required")
    rows=[]
    for seed in seeds:
        digest=sha256(f"{checkpoint_sha}|{state_key}|{k}|{seed}".encode()).digest()
        local=int.from_bytes(digest[:8],"big")
        basis=random_basis(d,k,local)
        x=score_state(T,basis,jacobians)
        # Hash the projector, rather than QR columns: basis changes in the
        # same subspace do not count as independent null subspaces.
        projector=matmul(basis,transpose(basis))
        projector_repr="|".join(
            f"{v:.10f}" for row in projector for v in row)
        subspace_sha=sha256(projector_repr.encode()).hexdigest()
        rows.append({"seed":seed,"basis_subspace_sha256":subspace_sha,
                     **{z:x[z] for z in
                   ("A_normalized","B_normalized","C_normalized","s_causal")}})
    return {"n":len(rows),"distinct_subspaces":len({
                row["basis_subspace_sha256"] for row in rows}),
            "d":d,"k":k,"sampling":"SHA256-keyed Gaussian/QR",
            "rows":rows}


def rank_p(actual,null,*,smaller):
    if len(null)<100:
        raise ValueError("At least 100 ranks needed")
    return (1+sum((x<=actual if smaller else x>=actual) for x in null))/(len(null)+1)


def holm(pvals):
    if any(p<0 or p>1 for p in pvals):
        raise ValueError("Invalid p")
    order=sorted(range(len(pvals)),key=lambda i:(pvals[i],i))
    q=[1.]*len(pvals);running=0.
    for j,i in enumerate(order):
        running=max(running,min(1.,(len(pvals)-j)*pvals[i]))
        q[i]=running
    return q


def norm_match(direction,random_direction):
    if not direction or len(direction)!=len(random_direction):
        raise ValueError("Vectors must be nonempty and equal length")
    a=sqrt(dot(direction,direction));b=sqrt(dot(random_direction,random_direction))
    if min(a,b)<=1e-12:
        raise ValueError("Zero direction")
    return [float(x)*a/b for x in random_direction]


def calibrate_state(card, null):
    """Prospective ROC-02 rank-conditioned, six-direction Holm tags.

    Raw normalized metrics and old absolute cutoff tags are retained for
    historical replay, but have no prospective inferential standing.
    """
    names=("A_normalized","B_normalized","C_normalized","s_causal")
    rows=null.get("rows",[])
    hashes=[row.get("basis_subspace_sha256") for row in rows]
    if (len(rows)<100 or len(hashes)!=len(set(hashes)) or
            any(h is None for h in hashes) or
            null.get("distinct_subspaces")!=len(set(hashes)) or
            null.get("d")!=card["d"] or null.get("k")!=card["k"] or
            any(set(names)-set(row) for row in rows)):
        return {"tags":["unclassified"],"tag_status":"insufficient_distinct_rank_null",
                "b_penalty_ratio_squared":None}
    med={}
    samples={}
    for name in names:
        values=[row[name] for row in rows]
        if any(v is None or not isfinite(v) for v in values):
            med[name]=None
            continue
        samples[name]=values
        med[name]=median(values)
    if card.get("zero_dynamics") or card.get("s_causal") is None:
        return {"tags":["unclassified"],"tag_status":"zero_dynamics_or_H",
                "null_medians":med,"b_penalty_ratio_squared":None}
    a,b,c,sc=(card[name] for name in names)
    def ratio(x,den):
        return x/den if den is not None and den>1e-12 else None
    ratios={"a":ratio(a,med["A_normalized"]),
            "b":ratio(b,med["B_normalized"]),
            "c":ratio(c,med["C_normalized"]),
            "s_low":ratio(sc,med["s_causal"]),
            "s_high":ratio(sc-med["s_causal"],1-med["s_causal"])
                       if med["s_causal"] is not None else None}
    directions=(("a_small","A_normalized",True),
                ("b_small","B_normalized",True),
                ("c_small","C_normalized",True),
                ("b_large","B_normalized",False),
                ("s_high","s_causal",False),
                ("s_low","s_causal",True))
    rawp={}
    for label,name,smaller in directions:
        values=samples.get(name)
        is_constant=(values is None or max(values)-min(values)<=1e-12)
        rawp[label]=(1. if is_constant else
                     rank_p(card[name],values,smaller=smaller))
    q=dict(zip(rawp,holm(list(rawp.values()))))
    def met(test,ratio_name,threshold,low=True):
        v=ratios.get(ratio_name)
        return (v is not None and
                (v<=threshold if low else v>=threshold)
                and q[test]<=0.05)
    A=met("a_small","a",0.20)
    Bs=met("b_small","b",0.20)
    C=met("c_small","c",0.20)
    Bl=met("b_large","b",1.20,False)
    Sh=met("s_high","s_high",0.80,False)
    Sl=met("s_low","s_low",0.20)
    tags=[]
    if Bs: tags.append("closed_quotient")
    if C: tags.append("invariant_subspace")
    if A and Bs and Sh: tags.append("latched_memory")
    if Bl and A and C: tags.append("output_register")
    if A and Bs and Sl: tags.append("irrelevant")
    return {"tags":tags or ["unclassified"],"tag_status":"null_calibrated",
            "null_medians":med,"effect_ratios":ratios,
            "one_sided_p":rawp,"holm_adjusted_p":q,
            "distinct_null_subspaces":null["distinct_subspaces"],
            "b_penalty_ratio_squared":
                ratios["b"]**2 if ratios["b"] is not None else None,
            "schema":"roc01.null_relative_six_direction.v1"}
