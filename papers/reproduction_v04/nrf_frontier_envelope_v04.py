"""Exact-decimal NRF post-review penalty frontier and selected-arm threshold audit.

Inputs:
  v03 skip_adjusted_frontier CSV (six depth-32 models, all gamma candidates)
  v02 NRF10 compact receipts CSV (original selected models)
  v02 NRF11 full receipts JSONs (fresh fold selected models)

Compute six-seed mean E+lambda mean(L^2) for each *whole arm* before
computing pairwise cuts. The minimizer is the lower envelope, not a list
of thresholds against task-only. All post-review sweeps are exploratory.
"""
from __future__ import annotations
import argparse,csv,json
from fractions import Fraction as Q
from pathlib import Path

ARMS=('gamma=0','gamma=0.05','gamma=0.2','gamma=1','task_free_supervised_start','task_free_random_start')
SEEDS=(131,137,139,149,151,157)

def source_rows(path):
    with Path(path).open(newline='',encoding='utf-8') as f:
        return list(csv.DictReader(f))

def score_lines(rows):
    lines={}
    for arm in ARMS:
        cohort=[r for r in rows if r['arm']==arm]
        if sorted(int(r['seed']) for r in cohort)!=list(SEEDS):
            raise ValueError(f'arm {arm} missing or duplicated model seeds')
        E=sum((Q(str(r['mse'])) for r in cohort),Q(0))/len(cohort)
        S=sum((Q(str(r['leakage']))**2 for r in cohort),Q(0))/len(cohort)
        lines[arm]=(E,S)
    return lines

def crossing(a,b):
    E1,L1=a;E2,L2=b
    return (E2-E1)/(L1-L2) if L1!=L2 else None

def intersections(lines):
    candidates={Q(0)}
    for i,k in enumerate(ARMS):
        for j in ARMS[i+1:]:
            x=crossing(lines[k],lines[j])
            if x is not None and x>0:candidates.add(x)
    return sorted(candidates)

def winner(lines,lam):
    return min(ARMS,key=lambda a:(lines[a][0]+lam*lines[a][1],ARMS.index(a)))

def lower_envelope(lines):
    cuts=intersections(lines)
    intervals=[]
    for left,right in zip(cuts,cuts[1:]+[None]):
        x=(left+right)/2 if right is not None else left+1
        w=winner(lines,x)
        if not intervals or intervals[-1]['winner']!=w:
            intervals.append({'start':float(left),'winner':w})
    # At the start of each interval, the optimum may be tied. Record exact cuts as fractions.
    for i in range(1,len(intervals)):
        a=intervals[i-1]['winner'];b=intervals[i]['winner']
        intervals[i]['exact_start']=str(crossing(lines[a],lines[b]))
        intervals[i]['start']=float(crossing(lines[a],lines[b]))
    return intervals

def selected_threshold(receipts,stage):
    seq=[]
    for seed in SEEDS:
        r=next(x for x in receipts if int(x['seed'])==seed and int(x['depth'])==32)
        seq.append(r)
    if stage=='NRF10':
        err_task=Q(0);err_joint=Q(0);l_task=Q(0);l_joint=Q(0)
        for r in seq:
            E0=Q(r['task_only_mse']);Ej=Q(r['joint_mse']);L0=Q(r['task_only_leakage']);Lj=Q(r['joint_leakage'])
            err_task+=E0;err_joint+=Ej;l_task+=L0*L0;l_joint+=Lj*Lj
    else:
        err_task=err_joint=l_task=l_joint=Q(0)
        for r in seq:
            a=r['arms']
            E0=Q(str(a['task_only']['heldout_mse']));Ej=Q(str(a['joint']['heldout_mse']))
            L0=Q(str(a['task_only']['local_fiber_leakage']));Lj=Q(str(a['joint']['local_fiber_leakage']))
            err_task+=E0;err_joint+=Ej;l_task+=L0*L0;l_joint+=Lj*Lj
    return {'lambda':float((err_joint-err_task)/(l_task-l_joint)),
            'mean_task_MSE':float(err_task/6),'mean_joint_MSE':float(err_joint/6),
            'mean_task_L_squared':float(l_task/6),'mean_joint_L_squared':float(l_joint/6)}

def selected_threshold_from_public_risk(rows,study):
    selected=[r for r in rows if r['study']==study and int(r['depth'])==32]
    if sorted(int(r['seed']) for r in selected)!=list(SEEDS):
        raise ValueError(f'incomplete {study} source risk cohort')
    E0=sum((Q(str(r['task_only_MSE'])) for r in selected),Q(0))/6
    E1=sum((Q(str(r['joint_MSE'])) for r in selected),Q(0))/6
    L0=sum((Q(str(r['task_only_leakage']))**2 for r in selected),Q(0))/6
    L1=sum((Q(str(r['joint_leakage']))**2 for r in selected),Q(0))/6
    return {'lambda':float((E1-E0)/(L0-L1)),
            'mean_task_MSE':float(E0),'mean_joint_MSE':float(E1),
            'mean_task_L_squared':float(L0),'mean_joint_L_squared':float(L1)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    paper=Path(__file__).resolve().parent.parent
    ap.add_argument('--frontier',type=Path,default=paper/'NRF_skip_adjusted_frontier_v03.csv')
    ap.add_argument('--selected-risk',type=Path,default=paper/'NRF_v04_selected_observer_risk.csv')
    ap.add_argument('--output',type=Path,default=paper/'NRF_v04_envelope_summary.json')
    opt=ap.parse_args()
    lines=score_lines(source_rows(opt.frontier))
    envelope=lower_envelope(lines)
    rows=source_rows(opt.selected_risk)
    original=selected_threshold_from_public_risk(rows,'NRF10')
    transfer=selected_threshold_from_public_risk(rows,'NRF11')
    result={'study':'NRF-01-11 v0.4 post-review objective envelope',
            'status':'retrospective, folds and model seeds previously examined',
            'lines':{a:{'mean_task_MSE':float(E),'mean_per_seed_leakage_squared':float(S)} for a,(E,S) in lines.items()},
            'lower_envelope':envelope,
            'pairwise_vs_gamma0':{a:float(crossing(lines['gamma=0'],lines[a])) for a in ARMS if a!='gamma=0'},
            'selected_thresholds':{'NRF10':original,'NRF11':transfer},
            'note':'Lower envelope uses complete seed-level means; cuts are exact rationals from decimal-source measurements.'}
    opt.output.parent.mkdir(parents=True,exist_ok=True)
    opt.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'frontier':envelope,'nrf10_lambda':original['lambda'],'nrf11_lambda':transfer['lambda']},indent=2))
if __name__=='__main__':main()
