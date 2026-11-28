"""Exploratory arithmetic controls added after the first COL-03 pilot.

Reads frozen target rows; recomputes predictors using d and unit-state count.
No refitting of the primary slope-six rule. Controls replace its geometric
direction by4 or8, or keep only the exact necessary cone A>=2u. Every arm
keeps the primary rule's period conversion A+2u. Comparisons isolate the
choice of a candidate pair from the same exact arithmetic lattice.
"""
import csv
import hashlib
import json
import math
from pathlib import Path
from statistics import median

from .arithmetic import branch_lattice

BASE=Path(__file__).parent


def alternative(d: int, units: int, slope: int | None) -> tuple[float,int,int]:
    lattice=branch_lattice(d)
    best=None
    for u in range(lattice.triple_stride,units+1,lattice.triple_stride):
        if slope is None:
            lower,upper=2*u,10**20
        else:
            width=math.isqrt(22*u)
            lower,upper=max(2*u,slope*u-width),slope*u+width
        residue=(u//lattice.triple_stride*lattice.halving_residue)%lattice.halving_period
        A=lower+(residue-lower)%lattice.halving_period
        if A>upper: continue
        # Keep the identical target-conversion A+2u to isolate candidate direction.
        candidate=(A+2*u,u,A)
        if best is None or candidate<best:best=candidate
    if best is None:raise ValueError('control has no admissible prediction')
    return best


def run() -> dict:
    source=BASE/'data/resonance_pilot.csv'
    records=list(csv.DictReader(source.open()))
    evaluation=[r for r in records if r['split']=='evaluation']
    results={}
    for name,slope in [('slope_four',4),('slope_eight',8),('necessary_cone_only',None)]:
        errors=[];primary_wins=control_wins=same_pair=0
        for row in evaluation:
            d,units=int(row['d']),int(row['unit_states'])
            prediction,u,A=alternative(d,units,slope)
            actual=float(row['observed_median_period'])
            error=abs(prediction-actual)/actual
            primary=abs(float(row['predicted_period'])-actual)/actual
            errors.append(error)
            primary_wins+=primary<error
            control_wins+=error<primary
            same_pair+=(u,A)==(int(row['predicted_u']),int(row['predicted_A']))
        results[name]={"parameters":len(evaluation),"median_relative_absolute_error":round(median(errors),9),
                       "primary_strict_wins":primary_wins,"control_strict_wins":control_wins,
                       "same_predicted_pair":same_pair}
    return {"schema":"mathcan.collatz.controls.v1",
            "status":"exploratory controls specified after observing the primary pilot",
            "candidate_period_conversion":"A+2u for all arms",
            "pilot_csv_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
            "results":results}


if __name__=='__main__':
    result=run()
    (BASE/'data/pilot_controls.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))
