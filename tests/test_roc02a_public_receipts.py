"""Standard-library audit of public ROC-02A retrospective rank-null receipts.

No PyTorch/checkpoint binaries needed; neural replay is covered by separate
source and tests in the downloadable original-byte reproduction package.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from pathlib import Path
from statistics import median,mean
import csv, gzip, json, math, hashlib, os, unittest

OUT=Path(os.environ.get('ROC02A_RECEIPT_DIR','research/observer_calculus/roc02a'))
SEEDS=(131,137,139,149,151,157)
DEPTHS=(16,32)
RANKS=(1,2,3,4,7,8,12,16,32)


def table(name):
    f=OUT/name
    if str(f).endswith('.gz'):
        with gzip.open(f,'rt',newline='') as h:return list(csv.DictReader(h))
    with f.open(newline='') as h:return list(csv.DictReader(h))


def pvalue(actual,null,less):
    return (1+sum(x<=actual if less else x>=actual for x in null))/129


def holm(ps):
    result=[1.]*len(ps); worst=0.
    for j,i in enumerate(sorted(range(len(ps)),key=lambda i:(ps[i],i))):
        worst=max(worst,min(1.,ps[i]*(len(ps)-j)))
        result[i]=worst
    return result


class ROC02APublic(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.nulls=table('roc02a_rank_nulls_compact.csv.gz')
        cls.obs=table('roc02a_rank_observers.csv')
        cls.byseed=table('roc02a_rank_by_seed.csv')
        cls.pareto=table('roc02a_3d_pareto_by_seed.csv')
        cls.summary=json.loads((OUT/'roc02a_retrospective_summary.json').read_text())
        cls.groups=defaultdict(list)
        for row in cls.nulls:
            cls.groups[tuple(map(int,(row['depth'],row['seed'],row['shadow_index'],row['rank'])))].append(row)

    def test_null_count_and_projector_distinctness(self):
        self.assertEqual(len(self.nulls),27648)
        self.assertEqual(len(self.groups),216)
        for key,rr in self.groups.items():
            self.assertEqual(len(rr),128)
            self.assertEqual(set(int(x['null_seed']) for x in rr),set(range(941001,941129)))
            self.assertEqual(len(set(x['projector_slice_sha256'] for x in rr)),128)
            self.assertTrue(all(len(x['projector_slice_sha256'])==32 for x in rr))

    def test_per_state_rank_p_median_and_holm(self):
        self.assertEqual(len(self.obs),480)
        for row in self.obs:
            key=tuple(map(int,(row['depth'],row['seed'],row['shadow_index'],row['rank'])))
            rr=self.groups[key]
            col={k:[float(x[k]) for x in rr] for k in ('a','b','c','s')}
            for k in ('a','b','c','s'):
                self.assertAlmostEqual(float(row['median_null_'+k]),median(col[k]),places=12)
            self.assertAlmostEqual(float(row['ratio_b']),float(row['b'])/median(col['b']),places=12)
            for k in ('a','b','c','s'):
                self.assertTrue(0<=float(row[k])<=1+1e-11)
            a,b,c,s=(float(row[x]) for x in ('a','b','c','s'))
            p=[pvalue(a,col['a'],True),pvalue(b,col['b'],True),
               pvalue(c,col['c'],True),pvalue(b,col['b'],False),
               pvalue(s,col['s'],False),pvalue(s,col['s'],True)]
            prefixes=('a_down','b_down','c_down','b_up','s_up','s_down')
            adj=holm(p)
            for pre,pv,qv in zip(prefixes,p,adj):
                self.assertAlmostEqual(pv,float(row['p_'+pre]),places=12)
                self.assertAlmostEqual(qv,float(row['holm_q_'+pre]),places=12)

    def test_rank_evidence_and_per_seed_direction(self):
        self.assertEqual(len(self.byseed),240)
        for depth in DEPTHS:
            for seed in SEEDS:
                for k in RANKS:
                    rr=[r for r in self.byseed if (int(r['depth']),int(r['seed']),int(r['rank']))==(depth,seed,k)]
                    self.assertEqual(len(rr),4 if k==8 else 2)
        for depth in DEPTHS:
            for seed in SEEDS:
                def value(arm,key):
                    return float(next(x for x in self.byseed if int(x['depth'])==depth and int(x['seed'])==seed and x['observer']==arm and int(x['rank'])==8)[key])
                self.assertLess(value('joint','ratio_b'),value('task_only','ratio_b'))
                self.assertGreater(value('joint','task_mse'),value('task_only','task_mse'))
                if depth==32:
                    self.assertLess(value('joint','s'),value('task_only','s'))

    def test_3d_pareto_is_true_nondominated(self):
        self.assertEqual(len(self.pareto),240)
        by=defaultdict(list)
        for x in self.pareto:by[int(x['depth']),int(x['seed'])].append(x)
        for key,rows in by.items():
            self.assertEqual(len(rows),20)
            for x in rows:
                k=float(x['rank']);E=float(x['task_mse']);B=float(x['b_over_null_median'])
                dominates=sum(float(y['rank'])<=k and float(y['task_mse'])<=E and float(y['b_over_null_median'])<=B
                  and (float(y['rank'])<k or float(y['task_mse'])<E or float(y['b_over_null_median'])<B)
                  for y in rows if y is not x)
                self.assertEqual(dominates,int(x['dominator_count']))
                self.assertEqual(x['three_dimensional_nondominated']=='True',dominates==0)

    def test_summary_and_manifest(self):
        self.assertEqual(self.summary['n_null_records'],27648)
        self.assertEqual(self.summary['n_observer_records'],480)
        manifest=json.loads((OUT/'roc02a_manifest.json').read_text())
        for filename,digest in manifest['files_sha256'].items():
            value=hashlib.sha256((OUT/filename).read_bytes()).hexdigest()
            self.assertEqual(value,digest,filename)
        for d in DEPTHS:
            v=self.summary['measurements'][str(d)]['rank8_arms']
            for observer in ('task_only','joint'):
                subset=[r for r in self.byseed if int(r['depth'])==d and r['observer']==observer]
                self.assertAlmostEqual(mean(float(x['s']) for x in subset),v[observer]['s'],places=12)

if __name__=='__main__':unittest.main()