"""ROC-05A/B fresh-model-seed and causal primary arithmetic (stdlib only).

Source CSV files are byte-identical copies from the merged LoopedTransformers
ROC-05A first training run and preregistered ROC-05B causal comparison.
Inferences concern ROC-05 exposed development cases, with reserved tests
never opened by these analyses.
"""
from __future__ import annotations
import csv
import hashlib
import itertools
import json
from pathlib import Path
from statistics import mean

HERE=Path(__file__).resolve().parent
A=HERE/"ROC05A_fresh_replication_by_seed_v01.csv"
B=HERE/"ROC05B_causal_primary_by_seed_v01.csv"
BLOBS={
 A.name:"a7954cf46f2f4e5e669b06f155a6f4906a0afc0b",
 B.name:"2ff367f0d5c9a316d91d7a4f38619c34ebce617e",
}
SEEDS=(20261117231,20261117233,20261117239,
       20261117241,20261117251,20261117257)
N=256

def checked_rows(path):
    raw=path.read_bytes()
    actual=hashlib.sha1(f"blob {len(raw)}".encode()+bytes([0])+raw).hexdigest()
    if actual!=BLOBS[path.name]:
        raise AssertionError("original Git blob bytes changed "+path.name)
    with path.open(newline="",encoding="utf-8") as f:
        data=list(csv.DictReader(f))
    if tuple(int(x["seed"]) for x in data)!=SEEDS:
        raise AssertionError("incomplete, reordered or duplicated model seeds")
    return data

def signflip(diffs):
    measured=mean(diffs)
    outcomes=[mean(sign*d for sign,d in zip(signs,diffs))
              for signs in itertools.product((-1,1),repeat=len(diffs))]
    more=sum(val>=measured-1e-15 for val in outcomes)
    return more,len(outcomes),more/len(outcomes)

def verify():
    adata=checked_rows(A)
    bdata=checked_rows(B)
    diffsA=[]
    diffsB=[]
    totals={"low":0,"high":0,"whole":0,"legal_high":0,"legal_low":0}
    per_seed=[]
    for a,b in zip(adata,bdata):
        if int(a["dev_cases"])!=N or int(b["paired_eligible"])!=N:
            raise AssertionError("256 dev cases or paired eligibility changed")
        low=int(a["low_correct"])
        high=int(a["high_correct"])
        whole=int(a["high_whole_table_count"])
        if not all(0<=v<=N for v in (low,high,whole)):
            raise AssertionError("invalid integer task table count")
        if (int(b["native_correct_high"])!=high or
            int(b["native_correct_low"])!=low):
            raise AssertionError("original task/model cohort differs from causal test")
        for k,n in (("low_accuracy",low),("high_accuracy",high),
                    ("high_whole_table_accuracy",whole)):
            if abs(float(a[k])-n/N)>1e-14:
                raise AssertionError("count/rate mismatch "+k)
        diffa=(high-low)/N
        if abs(diffa-float(a["paired_gain"]))>1e-14:
            raise AssertionError("ROC05A paired task gain mismatch")
        ob=float(b["observed_rule_margin_gain_high"])
        inp=float(b["soft_input_margin_gain_high"])
        diffb=float(b["observed_minus_soft_high"])
        if abs((ob-inp)-diffb)>1e-12:
            raise AssertionError("ROC05B physical matched-margin contrast changed")
        diffsA.append(diffa)
        diffsB.append(diffb)
        totals["low"]+=low
        totals["high"]+=high
        totals["whole"]+=whole
        totals["legal_high"]+=int(b["legal_full_changed_correct_high"])
        totals["legal_low"]+=int(b["legal_full_changed_correct_low"])
        per_seed.append({"seed":int(a["seed"]),"dev_task_gain":diffa,
                         "hidden_minus_input":diffb,
                         "high_complete_table_fraction":whole/N})
    assert totals=={"low":315,"high":1147,"whole":206,
                    "legal_high":1157,"legal_low":326},totals
    xA=signflip(diffsA)
    xB=signflip(diffsB)
    assert xA==(1,64,1/64),xA
    assert xB==(64,64,1.0),xB
    assert all(v>0 for v in diffsA)
    assert all(v<0 for v in diffsB)
    assert abs(mean(diffsA)-832/1536)<1e-15
    assert abs(mean(diffsB)-(-.06805337873205038))<1e-12
    assert sum(float(a["high_accuracy"])>=.70 for a in adata)==6
    assert sum(float(a["high_whole_table_accuracy"])>=.50 for a in adata)==0
    return {
        "study":"ROC-05A fresh source/model-seed replication + ROC-05B causal dev diagnostic",
        "six_model_initialization_seeds":len(SEEDS),
        "development_cases_per_seed":N,
        "roc05a_dev_accuracy_low":totals["low"]/(6*N),
        "roc05a_dev_accuracy_high":totals["high"]/(6*N),
        "roc05a_paired_accuracy_gain":mean(diffsA),
        "roc05a_positive_seeds":sum(v>0 for v in diffsA),
        "roc05a_exact_one_sided_signflip":xA[2],
        "roc05a_primary_gate":"PASS",
        "roc05a_mean_complete_table_accuracy":totals["whole"]/(6*N),
        "roc05a_competence_gate":"FAIL",
        "roc05b_primary_mean_observed_minus_input":mean(diffsB),
        "roc05b_positive_seeds":sum(v>0 for v in diffsB),
        "roc05b_exact_one_sided_signflip":xB[2],
        "roc05b_primary_gate":"FAIL",
        "roc05b_legal_changed_target_accuracy_high":totals["legal_high"]/(6*N),
        "roc05b_legal_changed_target_accuracy_low":totals["legal_low"]/(6*N),
        "roc05b_paired_eligible_per_model":N,
        "roc05_reserved_test_evaluated":False,
        "original_roc02_sealed_family6_7_evaluated":False,
        "results":per_seed,
    }

if __name__=="__main__":
    print(json.dumps(verify(),sort_keys=True,indent=2))
