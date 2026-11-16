"""NRF v0.5 audit: per-seed eight-random-arm references and study break-evens.

Reads only the files already published in MathCan paper PR #87. Pure Python,
no model checkpoints, PyTorch, or external dependencies. Does not constitute
an independent model rerun; every result is retrospective on NRF-11 fold 13.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from collections import defaultdict
from pathlib import Path
from statistics import mean

SCORES = ('incoming', 'outgoing', 'within_change', 'write_change', 'incoming_fraction')
SEEDS = (131, 137, 139, 149, 151, 157)
OBSERVERS = ('supervised', 'task_only', 'joint')
RANDOM_ARMS = tuple(f'random_{i}' for i in range(8))
STUDIES = ('NRF10', 'NRF11')


def load_csv(filename: Path):
    with filename.open(newline='', encoding='utf-8') as f:
        return list(csv.DictReader(f))


def check_receipts(root: Path):
    seed_rows = load_csv(root / 'NRF_v04_bidirectional_per_seed.csv')
    state_rows = load_csv(root / 'NRF_v04_bidirectional_per_state.csv')
    risk_rows = load_csv(root / 'NRF_v04_selected_observer_risk.csv')
    if (len(seed_rows), len(state_rows), len(risk_rows)) != (132, 1584, 24):
        raise AssertionError('expected 132 observer-seed, 1584 per-state and 24 risk rows')
    grouped = defaultdict(list)
    for row in state_rows:
        depth, seed, arm = int(row['depth']), int(row['seed']), row['arm']
        if depth not in (16, 32) or seed not in SEEDS or arm not in OBSERVERS + RANDOM_ARMS:
            raise AssertionError(f'unregistered state: {depth}, {seed}, {arm}')
        grouped[depth, seed, arm].append(row)
        def f(n): return float(row[n])
        if abs(f('write_change')**2 - f('within_change')**2 - f('incoming')**2) > 2e-12:
            raise AssertionError('incoming Pythagorean identity failed')
        if abs(f('origin_change')**2 - f('within_change')**2 - f('outgoing')**2) > 2e-12:
            raise AssertionError('outgoing Pythagorean identity failed')
    if len(grouped) != 132 or any(len(v) != 12 for v in grouped.values()):
        raise AssertionError('expected 12 shadow states for all 132 observed arms')
    if len({(r['depth'],r['seed'],r['arm']) for r in seed_rows}) != 132:
        raise AssertionError('duplicate or missing observer-seed row')
    for r in seed_rows:
        vals = grouped[int(r['depth']),int(r['seed']),r['arm']]
        for k in SCORES:
            if abs(float(r[k])-mean(float(v[k]) for v in vals)) > 1e-12:
                raise AssertionError('published observer-seed mean inconsistent: '+str((r['depth'], r['seed'], r['arm'], k)))
    return seed_rows, risk_rows


def build(root: Path):
    rows, risk = check_receipts(root)
    by_key = {(int(r['depth']),int(r['seed']),r['arm']):r for r in rows}
    risk_by_key = {(r['study'],int(r['depth']),int(r['seed'])):r for r in risk}
    records=[]
    def f(r,k):return float(r[k])
    for depth in (16,32):
        for seed in SEEDS:
            controls = [by_key[depth,seed,arm] for arm in RANDOM_ARMS]
            baselines = {k:mean(f(r,k) for r in controls) for k in SCORES}
            for arm in OBSERVERS:
                z=by_key[depth,seed,arm]
                r={'depth':depth, 'seed':seed,'arm':arm,
                   'selected_gamma':risk_by_key['NRF11',depth,seed]['selected_gamma'] if arm=='joint' else ''}
                for k in SCORES:
                    r[k]=f(z,k)
                    r['random_'+k]=baselines[k]
                    r[k+'_ratio_to_random']=f(z,k)/baselines[k]
                    r[k+'_vs_all_random']='above' if f(z,k)>max(f(v,k) for v in controls) else (
                        'below' if f(z,k)<min(f(v,k) for v in controls) else 'within')
                records.append(r)
    group_stats=[]
    for depth in (16,32):
        depth_rows=[r for r in rows if int(r['depth'])==depth]
        random_stats={k:mean(f(r,k) for r in depth_rows if r['arm'] in RANDOM_ARMS) for k in SCORES}
        for arm in ('random_mean',)+OBSERVERS:
            arm_rows=[r for r in depth_rows if r['arm']==arm] if arm!='random_mean' else []
            measures=random_stats if arm=='random_mean' else {k:mean(f(r,k) for r in arm_rows) for k in SCORES}
            out={'depth':depth,'arm':arm,'seed_count':6}
            for k in SCORES:
                out[k]=measures[k]
                out[k+'_over_random_mean']=measures[k]/random_stats[k]
            if arm in OBSERVERS:
                a=[x for x in records if x['depth']==depth and x['arm']==arm]
                out['arm_above_all_random_incoming']=sum(x['incoming_vs_all_random']=='above' for x in a)
                out['arm_below_all_random_incoming']=sum(x['incoming_vs_all_random']=='below' for x in a)
                out['arm_above_all_random_outgoing']=sum(x['outgoing_vs_all_random']=='above' for x in a)
                out['arm_below_all_random_outgoing']=sum(x['outgoing_vs_all_random']=='below' for x in a)
                out['arm_above_all_random_within']=sum(x['within_change_vs_all_random']=='above' for x in a)
                out['arm_below_all_random_within']=sum(x['within_change_vs_all_random']=='below' for x in a)
            group_stats.append(out)
    break_evens=[]
    for study in STUDIES:
        for depth in (16,32):
            sub=[r for r in risk if r['study']==study and int(r['depth'])==depth]
            if len(sub)!=6:raise AssertionError('missing independent seed risk')
            delta_mse=mean(float(r['joint_MSE'])-float(r['task_only_MSE']) for r in sub)
            delta_leak_sq=mean(float(r['task_only_leakage'])**2 - float(r['joint_leakage'])**2 for r in sub)
            if delta_leak_sq <= 0:raise AssertionError('unfavourable denominator')
            break_evens.append({'study':study,'depth':depth,'delta_MSE':delta_mse,
                                'delta_leakage_square':delta_leak_sq,
                                'break_even_lambda':delta_mse/delta_leak_sq})
    selected=[]
    for seed in SEEDS:
        r=risk_by_key['NRF11',32,seed]
        j=next(z for z in records if z['depth']==32 and z['seed']==seed and z['arm']=='joint')
        t=next(z for z in records if z['depth']==32 and z['seed']==seed and z['arm']=='task_only')
        selected.append({'seed':seed,'gamma':float(r['selected_gamma']),
                         'joint_vs_task_MSE_ratio':float(r['joint_MSE'])/float(r['task_only_MSE']),
                         'joint_within_over_random':j['within_change_ratio_to_random'],
                         'joint_incoming_over_random':j['incoming_ratio_to_random'],
                         'joint_outgoing_over_random':j['outgoing_ratio_to_random'],
                         'joint_incoming_fraction':j['incoming_fraction'],
                         'task_only_incoming_fraction':t['incoming_fraction'],
                         'joint_fraction_improves':j['incoming_fraction']<t['incoming_fraction']})
    if sum(r['joint_fraction_improves'] for r in selected)!=5:raise AssertionError('expected 5/6 selected fraction improvements')
    return records, {'study':'NRF-01–11 manuscript retrospective v0.5 audit',
                     'source':'public MathCan v0.4 per-state, per-seed and selected-risk files',
                     'numerical_scope':'NRF-11 shadow fold13 and task fold12; no model/optimizer rerun',
                     'group_means':group_stats,'break_evens':break_evens,
                     'depth32_selected_seed_details':selected,
                     'n_per_state_rows':1584,
                     'independent_model_seeds':6}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--output-dir',type=Path)
    p.add_argument('--verify',action='store_true')
    a=p.parse_args()
    data,summary=build(a.root)
    if a.output_dir:
        a.output_dir.mkdir(exist_ok=True,parents=True)
        with (a.output_dir/'NRF_v05_random_relative_by_seed.csv').open('w',newline='',encoding='utf-8') as f:
            w=csv.DictWriter(f,fieldnames=list(data[0]),lineterminator='\n');w.writeheader();w.writerows(data)
        (a.output_dir/'NRF_v05_random_relative_summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'n_rows':len(data),'break_evens':summary['break_evens'],
          'depth32_selected_seed_details':summary['depth32_selected_seed_details']},indent=2))

if __name__=='__main__': main()
