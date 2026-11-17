"""Recompute ROC-02A retrospective source summaries and rank tradeoffs."""
from pathlib import Path
from collections import defaultdict
import csv, json, statistics, hashlib
ROOT=Path(__file__).parent/'out'
SEEDS=(131,137,139,149,151,157)
DEPTHS=(16,32)
RANKS=(1,2,3,4,7,8,12,16,32)

def read(name):
    with (ROOT/name).open(newline='') as f:return list(csv.DictReader(f))

def write(name,rows):
    with (ROOT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def produce():
    rows=read('roc02a_rank_observers.csv')
    nulls=read('roc02a_rank_nulls.csv')
    stats=defaultdict(list)
    for r in rows:stats[int(r['depth']),int(r['seed']),int(r['rank']),r['observer']].append(r)
    byseed=[]
    for key,parts in sorted(stats.items()):
        if len(parts)!=2:raise AssertionError('unexpected state count')
        fields=('task_mse','task_mse_state','a','b','c','s','ratio_a','ratio_b','ratio_c','ratio_s',
                'finite_observed_effect','finite_dark_effect','finite_isotropic_effect',
                'linear_observed_residual','linear_dark_residual','linear_isotropic_residual','readout_ablation_risk_delta')
        v={col:statistics.mean(float(row[col]) for row in parts) for col in fields}
        byseed.append(dict(zip(('depth','seed','rank','observer'),key))|v|
            {'helm_b_down_count':sum(float(x['holm_q_b_down'])<=.05 for x in parts),
             'helm_s_up_count':sum(float(x['holm_q_s_up'])<=.05 for x in parts),
             'checkpoint_sha256':parts[0]['checkpoint_sha256'],
             'observer_adapter_sha256':parts[0]['observer_adapter_sha256']})
    write('roc02a_rank_by_seed.csv',byseed)
    pareto=[]
    for depth in DEPTHS:
        for seed in SEEDS:
            pool=[r for r in byseed if r['depth']==depth and r['seed']==seed]
            for x in pool:
                dom=[y for y in pool if y is not x and 
                     y['rank']<=x['rank'] and y['task_mse']<=x['task_mse'] and y['ratio_b']<=x['ratio_b'] and
                     (y['rank']<x['rank'] or y['task_mse']<x['task_mse'] or y['ratio_b']<x['ratio_b'])]
                pareto.append({'depth':depth,'seed':seed,'rank':x['rank'],'observer':x['observer'],
                     'task_mse':x['task_mse'],'b_over_null_median':x['ratio_b'],'s_output_capture':x['s'],
                     'three_dimensional_nondominated':not dom,'dominator_count':len(dom),
                     'objective':'retrospective 3D (rank, heldout MSE, rank-null-relative B); same models/folds'})
    write('roc02a_3d_pareto_by_seed.csv',pareto)
    null_groups=defaultdict(list)
    for row in nulls:null_groups[(int(row['depth']),int(row['seed']),int(row['shadow_index']),int(row['rank']))].append(row)
    null_q=[]
    for key,items in sorted(null_groups.items()):
        if len(items)!=128:raise AssertionError('wrong random count')
        def m(z):return statistics.median(float(item[z]) for item in items)
        null_q.append(dict(zip(('depth','seed','shadow_index','rank'),key))|
              {'null_count':128,'null_distinct_projector_fingerprints':len({x['projector_slice_sha256'] for x in items}),
               'median_a':m('a'),'median_b':m('b'),'median_c':m('c'),'median_s':m('s'),
               'null_seed_range':'941001..941128','raw_null_csv_sha256':hashlib.sha256((ROOT/'roc02a_rank_nulls.csv').read_bytes()).hexdigest()})
    write('roc02a_rank_null_medians.csv',null_q)
    metrics=['task_mse','ratio_b','s','ratio_s','finite_observed_effect','finite_dark_effect', 'readout_ablation_risk_delta']
    evidence={'study_id':'ROC-02A-RETRO-frozen-NRF-rank-causal-pilot-v1','model_seeds':list(SEEDS),'trained_depths':list(DEPTHS),
              'rank_grid':list(RANKS),'selected_shadow_indices':[0,1],
              'n_null_records':len(nulls),'n_observer_records':len(rows),'n_rank_seed_observer_records':len(byseed),
              'n_rank_seed_nondominated':sum(r['three_dimensional_nondominated'] for r in pareto),
              'measurements':{},'conclusion_scope':'retrospective frozen NRF, separately fitted train-only reference output head, two shadow states, previously exposed task fold 12'}
    for dep in DEPTHS:
        results={}
        for arm in ('supervised','pca','task_only','joint'):
            rr=[r for r in byseed if r['depth']==dep and r['rank']==8 and r['observer']==arm]
            results[arm]={key:statistics.mean(float(r[key]) for r in rr) for key in metrics}
            results[arm]['s_above_ranknull_significant_seed_states']=sum(int(r['helm_s_up_count']) for r in rr)
            results[arm]['b_below_ranknull_significant_seed_states']=sum(int(r['helm_b_down_count']) for r in rr)
        paired={}
        for key in metrics:
            diffs=[]
            for seed in SEEDS:
                def value(arm):return next(x for x in byseed if x['depth']==dep and x['seed']==seed and x['rank']==8 and x['observer']==arm)[key]
                diffs.append(value('joint')-value('task_only'))
            paired[key]={'joint_minus_task_only_by_seed':diffs,'negative_count':sum(x<0 for x in diffs),'positive_count':sum(x>0 for x in diffs)}
        evidence['measurements'][str(dep)]={'rank8_arms':results,'paired_deltas':paired}
    for f in ('roc02a_rank_by_seed.csv','roc02a_rank_null_medians.csv','roc02a_3d_pareto_by_seed.csv'):
        evidence.setdefault('public_receipt_hashes',{})[f]=hashlib.sha256((ROOT/f).read_bytes()).hexdigest()
    (ROOT/'roc02a_retrospective_summary.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    return evidence
if __name__=='__main__':
 r=produce();print(json.dumps({dep:r['measurements'][dep]['rank8_arms'] for dep in ['16','32']},indent=2))