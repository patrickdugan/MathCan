"""ROC-06A frozen train-only gradient-observer six-seed arithmetic (stdlib).

This uses the original public result CSV Git blob from merged
MoralityLabAI/LoopedTransformers #361, without opening any model or source
test examples. Signed margins are original frozen model logits on ROC05A dev.
"""
from __future__ import annotations
import csv,hashlib,itertools,json,math
from pathlib import Path
from statistics import mean

CSV=Path(__file__).with_name("ROC06A_gradient_primary_by_seed_v01.csv")
SOURCE_GIT_BLOB="66d7290f12ebdfe2e91dacdc55f3a4ff1dab525e"
SEEDS=(20261117231,20261117233,20261117239,
       20261117241,20261117251,20261117257)

def check():
    raw=CSV.read_bytes()
    git_hash=hashlib.sha1(f"blob {len(raw)}".encode()+bytes([0])+raw).hexdigest()
    if git_hash!=SOURCE_GIT_BLOB:raise AssertionError("original source Git blob mismatch")
    with CSV.open(newline="",encoding="utf-8") as f:
        rows=list(csv.DictReader(f))
    if tuple(int(r["seed"]) for r in rows)!=SEEDS:
        raise AssertionError("frozen model seed set changed")
    effects=[];gradient=[];supervised=[];soft=[];legal=original=0
    for r in rows:
        if int(r["eligible"])!=256:raise AssertionError("missing physical route pairing")
        g=float(r["gradient_gain"]);sup=float(r["supervised_gain"]);inp=float(r["soft_input_gain"])
        if any(not math.isfinite(x) for x in (g,sup,inp)):
            raise AssertionError("nonfinite native logit margin")
        if abs(g-sup-float(r["gradient_minus_supervised"]))>1e-12:
            raise AssertionError("gradient-supervised comparison mismatch")
        if abs(g-inp-float(r["gradient_minus_soft_input"]))>1e-12:
            raise AssertionError("gradient-input comparison mismatch")
        if r["best_reference"]!=("supervised_observed" if sup>=inp else "input_soft"):
            raise AssertionError("registered comparator changed")
        d=g-max(sup,inp)
        if abs(d-float(r["gradient_minus_best"]))>1e-12:
            raise AssertionError("gradient-best comparison mismatch")
        gradient.append(g);supervised.append(sup);soft.append(inp);effects.append(d)
        original+=int(r["original_correct"]);legal+=int(r["legal_changed_correct"])
    outcome=mean(effects)
    outcomes=[mean(a*b for a,b in zip(signs,effects))
              for signs in itertools.product((-1,1),repeat=6)]
    extreme=sum(x>=outcome-1e-15 for x in outcomes)
    p=extreme/64
    delta=[g-s for g,s in zip(gradient,supervised)]
    reverse_extreme=sum(x>=mean(delta)-1e-15 for x in
        [mean(a*b for a,b in zip(signs,delta))
         for signs in itertools.product((-1,1),repeat=6)])
    assert len(effects)==6
    assert (original,legal)==(1147,1157)
    assert all(d<0 for d in effects) and all(d>0 for d in delta)
    assert (extreme,p,reverse_extreme)==(64,1.,1)
    assert abs(outcome+0.0566440431951681)<1e-12
    assert abs(mean(delta)-0.011409252462423561)<1e-12
    assert abs(mean(gradient)-0.12937700875287797)<1e-12
    assert abs(mean(supervised)-0.11796775629045442)<1e-12
    assert abs(mean(soft)-0.18602105194804608)<1e-12
    return {
        "experiment":"ROC-06A-train-only-counterfactual-gradient-observer",
        "status":"registered primary FAIL",
        "mean_gradient_margin_gain":mean(gradient),
        "mean_supervised_margin_gain":mean(supervised),
        "mean_soft_input_margin_gain":mean(soft),
        "gradient_minus_supervised_mean":mean(delta),
        "gradient_minus_best_reference_mean":outcome,
        "gradient_over_supervised_positive_seeds":sum(d>0 for d in delta),
        "gradient_over_best_positive_seeds":sum(d>0 for d in effects),
        "registered_one_sided_signflip_p":p,
        "secondary_one_sided_signflip_p_descriptive":reverse_extreme/64,
        "eligible_per_seed":256,
        "legal_edited_correct":legal,
        "unedited_correct":original,
        "source_git_blob":SOURCE_GIT_BLOB,
        "roc05_reserved_test_opened":False,
        "original_roc02_family_6_7_opened":False,
    }

if __name__=="__main__":
    print(json.dumps(check(),sort_keys=True,indent=2))
