"""Post-pilot tail audit and exact short-cycle family excluded by the band."""
import argparse
from collections import Counter
import csv
from fractions import Fraction
import hashlib
import json
from math import ceil
from pathlib import Path
from statistics import mean, median

from .collatz_core import analyze, odd_step

BASE=Path(__file__).parent


def run() -> dict:
    path=BASE/'data/resonance_pilot.csv'
    rows=[r for r in csv.DictReader(path.open()) if r['split']=='evaluation']
    metrics={}
    for name,prediction in [('lattice','predicted_period'),('size','size_prediction')]:
        errors=sorted(abs(Fraction(r[prediction])-Fraction(r['observed_median_period']))/
                      Fraction(r['observed_median_period']) for r in rows)
        metrics[name]={
            'parameters':len(errors),'median_relative_absolute_error':round(float(median(errors)),9),
            'mean_relative_absolute_error':round(float(mean(errors)),9),
            'p90_nearest_rank':round(float(errors[ceil(.9*len(errors))-1]),9),
            'p95_nearest_rank':round(float(errors[ceil(.95*len(errors))-1]),9),
            'maximum_relative_absolute_error':round(float(max(errors)),9),
            'relative_error_greater_than_one':sum(e>1 for e in errors)}
    worst=max(rows,key=lambda r:Fraction(r['lattice_relative_absolute_error']))
    d=int(worst['d'])
    families=Counter((c['triple_branches'],c['halvings']) for c in analyze(d).cycles if c['gcd_with_d']==1)
    # The identity3+d=2^a proves the infinite family; replay checks the encoding.
    family=[]
    for a in range(2,21):
        parameter=2**a-3
        if odd_step(1,parameter)!=(1,a,1):raise AssertionError('short-cycle identity failed')
        family.append({'a':a,'d':parameter,'odd_fixed_point':1,'full_period':a+1,
                       'inside_primary_band':(a-6)**2<=22})
    return {'schema':'mathcan.collatz.pilot-tail-audit.v1',
            'status':'descriptive analysis added after the primary pilot',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'pilot_csv_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'sampling_measure':'one equally weighted median-unit-cycle-period target per parameter',
            'metrics':metrics,
            'worst_lattice_case':{**worst,'unit_cycle_families':[{'u':u,'A':A,'cycles':count} for (u,A),count in sorted(families.items())]},
            'fixed_point_family':family,
            'family_theorem':'For integer a>=2 and d=2^a-3, F_d(1)=1 with (u,A,r)=(1,a,1). For a>=11 its pair fails (A-6u)^2<=22u.',
            'scope':'The family proves exclusion of actual cycles. The finite census separately determines the median-period prediction error.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    data=run();output=BASE/'data/pilot_diagnostics.json'
    if args.check:
        if data!=json.loads(output.read_text()):raise SystemExit('tail receipt differs')
    else:output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'metrics':data['metrics'],'worst_case':data['worst_lattice_case']},indent=2))
