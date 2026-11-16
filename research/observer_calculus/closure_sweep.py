"""ROC-01 readout-containing closure sweep from a *provided* measured T and G.

Requires NumPy and a JSON source containing frozen checkpoint, state,
T=D(F^n)(h), and G=readout derivative at the declared state/horizon.
This module never fabricates an NRF/SPC checkpoint. No model data is bundled.

Reports:
  lower: exact finite-horizon SVD lower bound (up to floating error)
  upper: best of one output-observability SVD completion + 128 seeded
         conditionally random readout-containing rank-k completions
  interval: [lower, upper] containing L*(k) if the recorded T,G are valid
  p: rank-based one-sided placement of best deterministic SVD candidate
     among the 128 conditional random completions.
It does NOT claim the sampled upper bound equals the global optimum.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import argparse
import json
from math import isfinite

RANK_GRID=(1,2,3,4,7,8,12,16,32)
NULL_SEEDS=tuple(range(941001,941129))


def sweep(T,G,*,state_id,checkpoint_sha256,output_name,horizon=None):
    try:
        import numpy as np
    except ImportError as e:
        raise RuntimeError("NumPy is needed for real checkpoint matrix sweeps") from e
    T=np.asarray(T,dtype=np.float64)
    G=np.asarray(G,dtype=np.float64)
    if (T.ndim!=2 or T.shape[0]!=T.shape[1] or G.ndim!=2
            or G.shape[1]!=T.shape[0] or T.shape[0]<2
            or not (np.isfinite(T).all() and np.isfinite(G).all())
            or not all((state_id,checkpoint_sha256,output_name))):
        raise ValueError("Require finite square T and declared readout G with source IDs")
    d=T.shape[0]
    N=d if horizon is None else horizon
    if not isinstance(N,int) or not 2<=N<=d:
        raise ValueError("2<=horizon<=d needed; full d gives exact observable rank")
    r=np.linalg.matrix_rank(G,tol=1e-10)
    # Complete rowspace basis by SVD, U0 spans observed readout directions.
    _,_,vh=np.linalg.svd(G,full_matrices=True)
    R=vh[:r,:].T
    K=vh[r:,:].T
    normD=float(np.linalg.norm(T-np.eye(d),ord="fro"))
    powT=np.eye(d)
    blocks=[]
    for j in range(N):
        blocks.append(G@powT)
        powT=powT@T
    O=np.concatenate(blocks,axis=0)
    sig=np.linalg.svd(O,compute_uv=False)
    # Stronger operator-norm version of the same finite-horizon proof.
    M2=float(np.linalg.norm(T,ord=2)**2)
    fact=float(np.linalg.norm(G,ord="fro")**2 *
               sum(j*j*M2**(j-1) for j in range(1,N)))
    factor=fact**.5 if isfinite(fact) and fact>0 else float("inf")
    oK=O@K
    _,_,vk=np.linalg.svd(oK,full_matrices=True)
    ans=[]
    for k in RANK_GRID:
        if k>d:
            ans.append({"k":k,"status":"rank_exceeds_dimension"});continue
        if k<r:
            ans.append({"k":k,"status":"rank_below_declared_readout",
                        "required_readout_rank":int(r)});continue
        def get_B(U):
            P=U@U.T
            return float(np.linalg.norm(U.T@T@(np.eye(d)-P),ord="fro"))
        def complete(Z):
            U=np.concatenate([R,K@Z],axis=1) if Z.size else R.copy()
            if U.shape!=(d,k) or np.linalg.norm(U.T@U-np.eye(k))>1e-7:
                raise AssertionError("Admissible basis construction invalid")
            return U
        z=vk[:k-r,:].T if k-r else np.empty((d-r,0))
        U=complete(z)
        deterministic=get_B(U)
        random=[]
        for seed in NULL_SEEDS:
            hash_bytes=sha256(f"{checkpoint_sha256}|{state_id}|{k}|{seed}".encode()).digest()
            generator=np.random.default_rng(int.from_bytes(hash_bytes[:8],"big"))
            if k-r:
                # Exact QR on a normal matrix, Haar on complement subspace.
                W,_=np.linalg.qr(generator.normal(size=(d-r,k-r)))
            else:
                W=np.empty((d-r,0))
            random.append(get_B(complete(W)))
        best=min([deterministic]+random)
        # A G-containing rank-k basis has no free orientation when k=rank(G)
        # (nor when k=d). More generally an invariant T can give a constant
        # null distribution. In any such case a Monte Carlo rank has no
        # inferential meaning: the repeated samples are not distinct probes.
        conditional_null_degenerate=(
            k==r or k==d or
            max(random)-min(random) <= 1e-12*max(1.,max(random))
        )
        tail=float(np.sqrt(np.sum(sig[k:]**2)))
        lower=tail/factor if isfinite(factor) and factor>0 else 0.
        # Numerical bound can be slightly violated at roundoff.
        if lower>best+1e-7*max(1.,best):
            raise AssertionError("Violation of observable SVD lower bound")
        ans.append({
          "k":k,"status":"sampled_upper_and_certified_theoretical_lower",
          "N":N,"readout_rank":int(r),
          "observability_rank_at_N":int(np.linalg.matrix_rank(O,tol=1e-9)),
          "L_lower_svd":lower,
          "L_upper_sampled":best,
          "L_svd_candidate":deterministic,
          "normalized_B_upper":best/normD if normD>0 else 0.,
          "random_count":len(random),
          "T_operator_norm":M2**0.5,
          "lower_bound_norm":"operator_2",
          "random_min":min(random),"random_median":float(np.median(random)),
          "random_max":max(random),
          "one_sided_rank_p_for_svd_candidate":
            None if conditional_null_degenerate else
            (1+sum(v<=deterministic for v in random))/(len(random)+1),
          "conditional_null_degenerate":conditional_null_degenerate,
          "sweep_is_global_optimum":False,
          "squared_cost_units":"Frobenius norm on physical state"
        })
    return {"schema":"roc01.closure_sweep.sampled_bounds.v2",
            "state_id":state_id,"checkpoint_sha256":checkpoint_sha256,
            "output_name":output_name,"state_dimension":d,
            "readout_rank":int(r),"horizon":N,
            "source_claim":"measured T and G required; no refitting",
            "rank_grid":RANK_GRID,
            "rows":ans}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--horizon",type=int,default=None)
    a=p.parse_args()
    blob=a.source.read_bytes()
    src=json.loads(blob)
    for key in ("T","G","state_id","checkpoint_sha256","output_name"):
        if key not in src:
            raise ValueError("Missing source key: "+key)
    result=sweep(src["T"],src["G"],state_id=src["state_id"],
                 checkpoint_sha256=src["checkpoint_sha256"],
                 output_name=src["output_name"],horizon=a.horizon)
    result["input_sha256"]=sha256(blob).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({row["k"]:row["status"] for row in result["rows"]},sort_keys=True))

if __name__=="__main__":
    main()
