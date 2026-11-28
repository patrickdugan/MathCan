"""ROC-05A/B exact six-seed empirical arithmetic and original-source hash verifier.

These are distinct registered tests:
ROC-05A source-diversity training intervention on a fresh exposed dev rule pool;
ROC-05B frozen rank-seven hidden-source steering versus equal-radius continuous
input sensitivity on that SAME previously exposed dev pool.
Both use six independent model initializations, not 256 independent models.
The ROC05 reserved 384 identities and original ROC02 families 6/7 stay unopened.
"""
from __future__ import annotations
import csv, hashlib, itertools, json
from pathlib import Path
from statistics import mean

HERE=Path(__file__).resolve().parent
SEEDS=(20261117231,20261117233,20261117239,20261117241,20261117251,20261117257)
SOURCES={
    "roc05a":("ROC05A_fresh_seed_primary_v01.csv",
             "a7954cf46f2f4e5e669b06f155a6f4906a0afc0b"),
    "roc05b":("ROC05B_matched_causal_primary_v01.csv",
             "2ff367f0d5c9a316d91d7a4f38619c34ebce617e"),
}

def rows(key):
    filename,expected=SOURCES[key]
    raw=(HERE/filename).read_bytes()
    blob=hashlib.sha1(f"blob {len(raw)}".encode()+bytes([0])+raw).hexdigest()
    if blob!=expected:
        raise AssertionError(f"{key} CSV differs from original merged LoopedTransformers Git blob")
    with (HERE/filename).open(newline="",encoding="utf-8") as f:
        table=list(csv.DictReader(f))
    if tuple(int(r["seed"]) for r in table)!=SEEDS:
        raise AssertionError(f"{key} unexpected model-seed identity/order")
    return table

def signflip(diffs):
    observed=mean(diffs)
    vals=[mean(sign*d for sign,d in zip(signs,diffs))
          for signs in itertools.product((-1,1),repeat=6)]
    extreme=sum(v>=observed-1e-15 for v in vals)
    return extreme,extreme/64

def audit():
    a=rows("roc05a")
    total_low=total_high=total_table=0
    delta=[]
    task_count=table_count=0
    for r in a:
        n=int(r["dev_cases"])
        if n!=256:raise AssertionError("ROC05A incorrect dev case count")
        lo=int(r["low_correct"]);hi=int(r["high_correct"])
        whole=int(r["high_whole_table_count"])
        assert all(0<=v<=n for v in (lo,hi,whole))
        for v,k in [(lo,"low_accuracy"),(hi,"high_accuracy"),(whole,"high_whole_table_accuracy")]:
            if abs(v/n-float(r[k]))>1e-14:
                raise AssertionError("ROC05A raw counts disagree with published rates")
        d=(hi-lo)/n
        if abs(d-float(r["paired_gain"]))>1e-14:
            raise AssertionError("ROC05A paired gain mismatch")
        delta.append(d)
        total_low+=lo;total_high+=hi;total_table+=whole
        task_count+=int(hi/n>=.70)
        table_count+=int(whole/n>=.50)
    k,p=signflip(delta)
    observed=mean(delta)
    positive=sum(v>0 for v in delta)
    assert (total_low,total_high,total_table)==(315,1147,206)
    assert observed==832/1536 and positive==6 and k==1 and p==.015625
    assert task_count==6 and table_count==0
    a_gate=positive>=5 and observed>=.2 and p<=.05
    table_gate=task_count>=5 and table_count>=5
    assert a_gate and not table_gate

    b=rows("roc05b")
    d2=[]
    obs=[]
    soft=[]
    low=[]
    legal_correct=original_correct=0
    for r in b:
        if int(r["paired_eligible"])!=256:
            raise AssertionError("ROC05B paired physical eligibility mismatch")
        a_val=float(r["observed_rule_margin_gain_high"])
        b_val=float(r["soft_input_margin_gain_high"])
        delta2=float(r["observed_minus_soft_high"])
        if abs((a_val-b_val)-delta2)>1e-12:
            raise AssertionError("ROC05B signed target-margin arithmetic mismatch")
        d2.append(delta2)
        obs.append(a_val)
        soft.append(b_val)
        low.append(float(r["observed_minus_soft_low"]))
        original_correct+=int(r["native_correct_high"])
        legal_correct+=int(r["legal_full_changed_correct_high"])
    extreme,p2=signflip(d2)
    effect=mean(d2)
    positive_b=sum(v>0 for v in d2)
    assert abs(effect-(-0.06805337873205038))<1e-12
    assert (extreme,p2,positive_b)==(64,1.,0)
    assert (original_correct,legal_correct)==(1147,1157)
    b_gate=positive_b>=5 and effect>0 and p2<=.05
    assert not b_gate
    return {
      "roc05a":{
        "study":"Fresh model-seed and train/development permutation pool",
        "seeds":6,"dev_cases_per_seed":256,
        "low_accuracy":total_low/(256*6),"high_accuracy":total_high/(256*6),
        "mean_accuracy_gain":observed,"positive_seed_count":positive,
        "one_sided_exact_p":p,"primary_gate":"PASS",
        "high_full_table_exact":total_table/(256*6),
        "high_task_70pct_seed_count":task_count,"high_table_50pct_seed_count":table_count,
        "competence_gate":"FAIL",
      },
      "roc05b":{
        "study":"Frozen original checkpoint physical L2 matched rule/input intervention",
        "seeds":6,"eligible_cases_per_high_seed":256,
        "mean_observed_margin_gain":mean(obs),"mean_soft_input_margin_gain":mean(soft),
        "observed_minus_input":effect,"positive_seed_count":positive_b,
        "one_sided_exact_p":p2,"primary_gate":"FAIL",
        "original_legal_task_correct":legal_correct,"original_native_correct":original_correct,
        "soft_input_off_discrete_manifold":True,
        "exposed_development_causal_diagnostic":True,
      },
      "roc05_reserved_cases_evaluated":False,
      "original_roc02_sealed_families_evaluated":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
