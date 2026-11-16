"""ROC-01 exact rational lower envelopes and three-coordinate Pareto surfaces.

For old NRF-v0.4 data, slopes are mean-per-seed squared raw leakage,
NOT normalized ROC ||B||². No conversion of units without per-state ||D||F.

A new ROC surface must provide rank, task MSE and normalized B per candidate;
the Pareto method refuses rows missing those measurements.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
from typing import Mapping, Sequence
import json
from pathlib import Path


def number(v):
    if isinstance(v, bool):
        raise ValueError("Boolean is not a numeric source")
    return F(str(v))


def lower_envelope(lines: Mapping[str, tuple[object,object]]) -> dict:
    """Complete min_i (E_i + λ L_i) for λ>=0, exact rational arithmetic."""
    if not lines:
        raise ValueError("Nonempty candidate list required")
    pool={name:(number(pair[0]),number(pair[1])) for name,pair in lines.items()}
    if any(s<0 for e,s in pool.values()):
        raise ValueError("Penalty slope must be nonnegative")
    cuts={F(0)}
    for a,b in combinations(pool,2):
        ea,sa=pool[a];eb,sb=pool[b]
        if sa!=sb:
            c=(eb-ea)/(sa-sb)
            if c>0:cuts.add(c)
    x=sorted(cuts)
    intervals=[]
    for i,bound in enumerate(x):
        probe=(bound+x[i+1])/2 if i+1<len(x) else bound+1
        candidate=min(pool,key=lambda name:(pool[name][0]+probe*pool[name][1],name))
        if not intervals or intervals[-1]["winner"]!=candidate:
            intervals.append({"start":bound,"winner":candidate})
    return {"intervals":intervals,
            "all_pairwise_crossings":sorted(c for c in cuts if c>0),
            "candidate_count":len(pool)}


def stringify_envelope(report):
    return [{"start":float(rec["start"]),"exact_start":str(rec["start"]),
             "winner":rec["winner"]} for rec in report["intervals"]]


def pareto_surface(points: Sequence[Mapping]) -> dict:
    """Nondominated (rank, task_error, normalized_B) rows.

    Each point must include actual normalized ROC B. Historical raw NRF
    leakage values cannot be silently used as normalized_B.
    """
    if not points: raise ValueError("Nonempty candidate surface required")
    items=[]
    for p in points:
        if any(k not in p for k in ("id","rank","task_error","normalized_B")):
            raise ValueError("Complete ROC surface coordinates required")
        if type(p["rank"]) is not int or p["rank"]<1:
            raise ValueError("Positive integer rank required")
        e,b=number(p["task_error"]),number(p["normalized_B"])
        if e<0 or b<0: raise ValueError("Nonnegative task and B required")
        items.append((p["id"],p["rank"],e,b))
    if len(set(x[0] for x in items))!=len(items):
        raise ValueError("Unique candidate IDs required")
    def dom(a,b):
        aa=a[1:];bb=b[1:]
        return all(x<=y for x,y in zip(aa,bb)) and any(x<y for x,y in zip(aa,bb))
    front=[x for x in items if not any(dom(y,x) for y in items if x!=y)]
    return {"n_candidates":len(items),"n_pareto":len(front),
            "pareto":sorted([x[0] for x in front]),
            "dominated":sorted([x[0] for x in items if x not in front])}


def inherited_v04_check(path=Path("papers/NRF_v04_envelope_summary.json")):
    report=json.loads(path.read_text(encoding="utf-8"))
    pool={k:(v["mean_task_MSE"],v["mean_per_seed_leakage_squared"])
          for k,v in report["lines"].items()}
    derived=stringify_envelope(lower_envelope(pool))
    prior=report["lower_envelope"]
    if [r["winner"] for r in derived]!=[r["winner"] for r in prior]:
        raise AssertionError("Historical lower envelope winners drift")
    if any(abs(r["start"]-q["start"])>1e-10 for r,q in zip(derived,prior)):
        raise AssertionError("Historical lower envelope switch points drift")
    return derived


if __name__=="__main__":
    print(json.dumps(inherited_v04_check(),indent=2))
