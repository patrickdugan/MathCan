"""Frozen out-of-range CPU pilot for the slope-six branch-lattice hypothesis.

Fit a log-linear size baseline on every admissible d in [5,1025]. Evaluate
every admissible d in [1029,8193]. The lattice rule selects the smallest
A+2u with u>0, A>=2u and (A-6u)^2<=22u, u at most the unit odd-core size.
The factor22 comes from the uniform2-adic one-step variance model.
The target is the median original-map period across unit cycles, with each
cycle weighted equally. This public finite pilot claims no neural result.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from statistics import median

from .arithmetic import BranchLattice, branch_lattice
from .collatz_core import analyze

BASE = Path(__file__).parent
CONFIG = {"development_d": [5,1025], "evaluation_d": [1029,8193],
          "parameter_step": 4, "gcd_d_6": 1,
          "slope": 6, "squared_deviation_coefficient": 22,
          "target": "median full-map period, equal weight per unit cycle",
          "candidate_rank": "(A+2u,u,A)",
          "baseline": "OLS log(median_period) ~ 1 + log(unit_odd_core_states)"}


def predict_pair(lattice: BranchLattice, max_u: int) -> tuple[int, int] | None:
    candidates=[]
    for u in range(lattice.triple_stride,max_u+1,lattice.triple_stride):
        tolerance=math.isqrt(22*u)
        lower=max(2*u,6*u-tolerance)
        upper=6*u+tolerance
        residue=(u//lattice.triple_stride*lattice.halving_residue)%lattice.halving_period
        A=lower+(residue-lower)%lattice.halving_period
        if A<=upper:
            candidates.append((A+2*u,u,A))
    if not candidates: return None
    _,u,A=min(candidates)
    return u,A


def observe(d: int) -> dict:
    # Both predictors receive arithmetic features before target enumeration.
    unit_states=sum(math.gcd(n,d)==1 for n in range(1,d+1,2))
    lattice=branch_lattice(d)
    pair=predict_pair(lattice,unit_states)
    core=analyze(d)
    cycles=[c for c in core.cycles if c['gcd_with_d']==1]
    if unit_states!=sum(c['basin_size'] for c in cycles):
        raise AssertionError('arithmetic unit count disagrees with finite graph')
    return {"d":d,"unit_states":unit_states,"unit_cycles":len(cycles),
            "unit_cycles_zero_triples":sum(c['triple_branches']==0 for c in cycles),
            "observed_median_period":median(c['period'] for c in cycles),
            "predicted_u":pair[0] if pair else None,
            "predicted_A":pair[1] if pair else None,
            "predicted_period":pair[1]+2*pair[0] if pair else None,
            "cycles_with_predicted_pair":sum((c['triple_branches'],c['halvings'])==pair for c in cycles)}


def fit_size_model(rows: list[dict]) -> tuple[float,float]:
    x=[math.log(r['unit_states']) for r in rows]
    y=[math.log(r['observed_median_period']) for r in rows]
    mx,my=sum(x)/len(x),sum(y)/len(y)
    slope=sum((a-mx)*(b-my) for a,b in zip(x,y))/sum((a-mx)**2 for a in x)
    return my-slope*mx,slope


def run() -> tuple[list[dict],dict]:
    rows=[]
    for split,bounds in (("development",CONFIG['development_d']),("evaluation",CONFIG['evaluation_d'])):
        for d in range(bounds[0],bounds[1]+1,4):
            if math.gcd(d,6)!=1: continue
            row=observe(d);row['split']=split;rows.append(row)
    intercept,slope=fit_size_model([r for r in rows if r['split']=='development'])
    for row in rows:
        size=math.exp(intercept+slope*math.log(row['unit_states']))
        actual=row['observed_median_period']
        row['size_prediction']=round(size,9)
        row['size_relative_absolute_error']=round(abs(size-actual)/actual,9)
        row['lattice_relative_absolute_error']=(round(abs(row['predicted_period']-actual)/actual,9)
                                               if row['predicted_period'] is not None else None)
    summaries={}
    for split in ('development','evaluation'):
        part=[r for r in rows if r['split']==split]
        covered=[r for r in part if r['predicted_period'] is not None]
        summaries[split]={
            "parameters":len(part), "parameters_with_prediction":len(covered),
            "unit_cycles":sum(r['unit_cycles'] for r in part),
            "cycles_with_predicted_pair":sum(r['cycles_with_predicted_pair'] for r in part),
            "parameters_with_any_predicted_pair_cycle":sum(r['cycles_with_predicted_pair']>0 for r in part),
            "median_relative_absolute_error_lattice_covered":median(r['lattice_relative_absolute_error'] for r in covered),
            "median_relative_absolute_error_size_same_covered":median(r['size_relative_absolute_error'] for r in covered),
            "lattice_strict_wins_on_covered":sum(r['lattice_relative_absolute_error']<r['size_relative_absolute_error'] for r in covered),
            "size_strict_wins_on_covered":sum(r['lattice_relative_absolute_error']>r['size_relative_absolute_error'] for r in covered),
            "unit_cycles_zero_triples":sum(r['unit_cycles_zero_triples'] for r in part)}
    return rows,{"schema":"mathcan.collatz.pilot.v1","config":CONFIG,
                 "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 "core_sha256":hashlib.sha256((BASE/'collatz_core.py').read_bytes()).hexdigest(),
                 "arithmetic_sha256":hashlib.sha256((BASE/'arithmetic.py').read_bytes()).hexdigest(),
                 "size_baseline":{"intercept":round(intercept,12),"log_slope":round(slope,12)},
                 "summaries":summaries,
                 "evidence":"finite public parameter extrapolation; rule fixed before evaluation run; no mechanistic or neural claim"}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=BASE/'data')
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    # Write the specification before touching evaluation targets.
    (args.output_dir/'pilot_frozen_spec.json').write_text(json.dumps({"config":CONFIG,"source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2,sort_keys=True)+'\n')
    rows,summary=run()
    with (args.output_dir/'resonance_pilot.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
    (args.output_dir/'resonance_pilot.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary['summaries'],indent=2))
