"""ROC-01 NRF v0.4 RETROSPECTIVE partial cards and six-seed decomposition.

Inputs are already public on the NRF paper branch. Per-shadow original
Frobenius blocks are divided by sqrt(k=8). No full D norm, H, per-state
task error, random-128-basis null, or new neural checkpoint appears here.

Decompose ΔB exactly at each matched state using a symmetric Shapley split:
  B = W rho
  mag = (W1-W0)(rho1+rho0)/2
  fraction = (rho1-rho0)(W1+W0)/2
  ΔB = mag+fraction.
Then average within model seed, then across six independent model seeds.
The product of averaged W and averaged rho is NOT the mean B.
"""
from __future__ import annotations
from collections import defaultdict
from pathlib import Path
from statistics import mean
import argparse
import csv
import json
import math

IN_STATE = Path("papers/NRF_v04_bidirectional_per_state.csv")
IN_RISK = Path("papers/NRF_v04_selected_observer_risk.csv")
IN_ENVELOPE = Path("papers/NRF_v04_envelope_summary.json")
OUT = Path("research/observer_calculus")

def read_rows(path):
    with path.open(newline="",encoding="utf-8") as file:
        return list(csv.DictReader(file))

def _float(row,k):
    return float(row[k])

def produce(state, risks, envelope):
    if len(state)!=1584:
        raise ValueError("Expected all 1584 public NRF11 state/arm rows")
    by_key = {}
    partial=[]
    for r in state:
        key=(int(r["depth"]),int(r["seed"]),int(r["shadow_index"]))
        if key not in by_key:
            by_key[key]={}
        if r["arm"] in by_key[key]:
            raise ValueError("Duplicate state/arm")
        by_key[key][r["arm"]]=r
        partial.append({
          "depth":r["depth"],"seed":r["seed"],"arm":r["arm"],
          "state_index":r["shadow_index"],"d":"128","k":"8",
          "A_frob_per_sqrtk":r["within_change"],
          "B_frob_per_sqrtk":r["incoming"],
          "C_frob_per_sqrtk":r["outgoing"],
          "W_delta_per_sqrtk":r["write_change"],
          "rho_delta":r["incoming_fraction"],
          "A_normalized":"","B_normalized":"","C_normalized":"",
          "H_trace":"","s_causal":"","task_mse_state":"",
          "null_count":"8","rank_p":"","rank_p_valid":"False",
          "classification":"not_scored","card_status":"retrospective_partial",
          "provenance":"NRF11_fold13_public_per_state_v04",
          "missing":"D_frob,H,per_state_task_MSE,128_basis_null,per_state_output_J"
        })
    risk={(r["study"],int(r["depth"]),int(r["seed"])):r for r in risks}
    expected_seeds=(131,137,139,149,151,157)
    seedrows=[]
    for depth in (16,32):
        for seed in expected_seeds:
            states=[by_key[(depth,seed,idx)] for idx in range(12)]
            for key in states:
                if not all(x in key for x in ("task_only","joint")):
                    raise ValueError("Missing paired task and joint")
            vals=[]
            for arms in states:
                a,b=arms["task_only"],arms["joint"]
                W0,W1=_float(a,"write_change"),_float(b,"write_change")
                q0,q1=_float(a,"incoming_fraction"),_float(b,"incoming_fraction")
                B0,B1=_float(a,"incoming"),_float(b,"incoming")
                mag=(W1-W0)*(q0+q1)/2
                frac=(q1-q0)*(W0+W1)/2
                if abs(mag+frac-(B1-B0))>1e-10:
                    raise AssertionError("Exact per-state ΔB identity failed")
                if abs(W0*q0-B0)>1e-10 or abs(W1*q1-B1)>1e-10:
                    raise AssertionError("Input shadow identity fails")
                vals.append(dict(
                  B_task=B0,B_joint=B1,delta_B=B1-B0,
                  magnitude_contribution=mag,fraction_contribution=frac,
                  W_task=W0,W_joint=W1,rho_task=q0,rho_joint=q1,
                  A_task=_float(a,"within_change"),A_joint=_float(b,"within_change"),
                  C_task=_float(a,"outgoing"),C_joint=_float(b,"outgoing")))
            v={k:mean(item[k] for item in vals) for k in vals[0]}
            gamma=float(risk[("NRF11",depth,seed)]["selected_gamma"])
            seedrows.append({
              "study":"NRF11","depth":depth,"seed":seed,"states":len(vals),
              "gamma":gamma,**v,
              "magnitude_share_abs":abs(v["magnitude_contribution"])/abs(v["delta_B"])
              if abs(v["delta_B"])>1e-14 else "",
              "status":"retrospective_same_model_fold13"
            })
    if len(seedrows)!=12 or len(partial)!=1584:
        raise AssertionError("Output cardinality drift")
    report={"schema":"roc01.nrf11.partial.retrospective.v1",
            "source_public_branch":"paper/nrf-observable-fibers-v02-20261115",
            "source_rows":len(partial),"paired_seeds":len(seedrows),
            "full_card_complete":False,
            "missing_card_fields":["full_D_frob","OLM07_H","per_state_task_MSE",
                                   "128_rank_matched_nulls","matched_norm_interventions"],
            "by_depth":{}}
    for depth in (16,32):
        d=[r for r in seedrows if r["depth"]==depth]
        names=("B_task","B_joint","delta_B","magnitude_contribution",
               "fraction_contribution","W_task","W_joint","rho_task",
               "rho_joint","C_task","C_joint")
        means={k:mean(r[k] for r in d) for k in names}
        report["by_depth"][str(depth)]={
          "model_seeds":expected_seeds,"counts":{
            "B_decreases":sum(r["delta_B"]<0 for r in d),
            "write_magnitude_contribution_negative":sum(r["magnitude_contribution"]<0 for r in d),
            "dark_fraction_contribution_negative":sum(r["fraction_contribution"]<0 for r in d),
            "C_decreases":sum(r["C_joint"]<r["C_task"] for r in d)},
          "means":means,
          "paired_seed_records":[{k:r[k] for k in
                                ("seed","gamma","delta_B","magnitude_contribution",
                                 "fraction_contribution")} for r in d]
        }
    report["historical_raw_lambda_envelope"]=[
        {"start":str(x["start"]),"winner":x["winner"]}
        for x in envelope["lower_envelope"]]
    report["envelope_metric"]="raw mean_per_seed_squared_leakage; NOT new normalized ROC B²"
    return partial,seedrows,report

def write_csv(path,rows):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--state",type=Path,default=IN_STATE)
    parser.add_argument("--risk",type=Path,default=IN_RISK)
    parser.add_argument("--envelope",type=Path,default=IN_ENVELOPE)
    parser.add_argument("--out-dir",type=Path,default=OUT)
    a=parser.parse_args()
    parsed=produce(read_rows(a.state),read_rows(a.risk),
                   json.loads(a.envelope.read_text()))
    partial,seeds,report=parsed
    write_csv(a.out_dir/"ROC01_NRF11_PER_STATE_PARTIAL.csv",partial)
    write_csv(a.out_dir/"ROC01_NRF11_PER_SEED_DECOMP.csv",seeds)
    (a.out_dir/"ROC01_NRF11_SUMMARY.json").write_text(
        json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report["by_depth"],sort_keys=True))

if __name__=="__main__":
    main()
