"""ROC-02A frozen NRF pilot: numeric, algebraic and receipt gates."""
import csv, hashlib, math, os, tempfile, unittest
from collections import Counter, defaultdict
from pathlib import Path
import torch
try:
    from research_gym.analysis.roc02a_frozen_rank_causal import (
        D,OUT,RADIUS,RANKS,SEEDS,DEPTHS,NULL_SEEDS,SHADOW_INDICES,
        load_cell,tangent,future_steps,seeded_basis,score_batch,pvalue,holm,
        basis_ridge_mse,projector_slice_sha)
except ModuleNotFoundError:
    from roc02a_frozen_rank_causal import (
    D,OUT,RADIUS,RANKS,SEEDS,DEPTHS,NULL_SEEDS,SHADOW_INDICES,
    load_cell,tangent,future_steps,seeded_basis,score_batch,pvalue,holm,
    basis_ridge_mse,projector_slice_sha)
ROOT=Path(__file__).resolve().parent
ARCHIVE_ROOT=Path(os.getenv("ROC02A_ARCHIVE_ROOT","/mnt/data/roc02_local"))
RECEIPT_DIR=Path(os.getenv("ROC02A_RECEIPT_DIR","/mnt/data/roc02_local/out"))

class ROC02AMathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):torch.set_num_threads(2)

    def test_direct_frobenius_blocks_and_gram(self):
        r=torch.Generator().manual_seed(701)
        M=torch.randn(D,D,generator=r,dtype=torch.float64)*.02
        G=torch.randn(OUT,D,generator=r,dtype=torch.float64)
        U=torch.linalg.qr(torch.randn(D,7,generator=r,dtype=torch.float64))[0]
        T=M+torch.eye(D,dtype=torch.float64)
        _,norms=0,score_batch(U.unsqueeze(0),G@T,M)[0].tolist()
        a,b,c,s,A,B,C=norms
        Q=torch.eye(D,dtype=torch.float64)-U@U.T
        self.assertAlmostEqual(A*A,float((U.T@M@U).square().sum()),places=9)
        self.assertAlmostEqual(B*B,float((U.T@M@Q).square().sum()),places=9)
        self.assertAlmostEqual(C*C,float((Q@M@U).square().sum()),places=9)
        self.assertAlmostEqual(a*a+b*b+c*c+float((Q@M@Q).square().sum())/float((M*M).sum()),1.,places=9)
        self.assertAlmostEqual(s,float(((G@T@U).square().sum())/((G@T).square().sum())),places=10)

    def test_128_rank_matched_null_reproducible_and_distinct(self):
        seed='f'*64
        for k in RANKS:
            fingerprints=set()
            for n in NULL_SEEDS:
                u=seeded_basis(seed,0,k,n)
                self.assertEqual(u.shape,(D,k))
                self.assertLess(float(torch.linalg.norm(u.T@u-torch.eye(k,dtype=torch.float64))),1e-10)
                fingerprints.add(projector_slice_sha(u))
            self.assertEqual(len(fingerprints),128)
        self.assertTrue(torch.equal(seeded_basis(seed,0,8,941001),seeded_basis(seed,0,8,941001)))
        self.assertFalse(torch.equal(seeded_basis(seed,0,8,941001),seeded_basis(seed,1,8,941001)))

    def test_rank_p_and_holm_family(self):
        x=[1.]*128
        self.assertEqual(pvalue(.5,x,True),1/129)
        self.assertEqual(pvalue(1.,x,True),1.)
        self.assertEqual(pvalue(1.,x,False),1.)
        q=holm([1/129]*6)
        self.assertEqual(q,[6/129]*6)
        self.assertTrue(all(y<=.05 for y in q))

class ROC02APilotReceipts(unittest.TestCase):
    def test_checkpoint_and_adapter_hashes(self):
        if not (ARCHIVE_ROOT/'nrf09_local'/'checkpoints').exists():
            self.skipTest('external binary archive required; local receipt/source tests still run')
        root=ARCHIVE_ROOT
        for d in DEPTHS:
            for seed in SEEDS:
                w,a,sha1,sha2=load_cell(root,seed,d)
                self.assertEqual(len(sha1),64)
                self.assertEqual(len(sha2),64)
                self.assertEqual(tuple(a['joint_basis'].shape),(D,OUT))

    def test_one_finite_difference_on_original_checkpoint(self):
        if not (ARCHIVE_ROOT/'nrf09_local'/'checkpoints').exists():
            self.skipTest('external archive required for finite-difference replay')
        try:
            from research_gym.analysis.roc02a_frozen_rank_causal import half_states,gaussian_inputs,train_data,train_output_head
        except ModuleNotFoundError:
            from roc02a_frozen_rank_causal import half_states,gaussian_inputs,train_data,train_output_head
        w,a,_,_=load_cell(ARCHIVE_ROOT,131,32)
        h,y,he,mh,my=train_data(w,131,32)
        W,_,_=train_output_head(he,y)
        x,_=gaussian_inputs(131,13,1)
        hm=half_states(w,x,32)[0]
        T,output=tangent(w,hm,16)
        self.assertLess(float((output-future_steps(w,hm,16)).norm()),1e-10)
        J=W.T@T
        g=torch.randn(D,dtype=torch.float64,generator=torch.Generator().manual_seed(73))
        for radius in (0.01,0.05,0.2):
            delta=g/g.norm()*radius
            actual=(future_steps(w,hm+delta,16)-output)@W
            error=float((actual-J@delta).norm())
            self.assertLess(error,0.02*radius)

    def test_public_rows_and_six_seed_comparisons(self):
        rdir=RECEIPT_DIR
        if not (rdir/'roc02a_rank_nulls.csv').exists():
            self.skipTest('full raw nulls in downloadable archive or compressed repo receipts')
        with (rdir/'roc02a_rank_nulls.csv').open() as handle:
            nulls=list(csv.DictReader(handle))
        with (rdir/'roc02a_rank_observers.csv').open() as handle:
            obs=list(csv.DictReader(handle))
        self.assertEqual(len(nulls),12*2*9*128)
        self.assertEqual(len(obs),12*2*(9*2+2))
        grp=defaultdict(list)
        for x in nulls:
            key=(x['depth'],x['seed'],x['shadow_index'],x['rank'])
            grp[key].append(x)
            for metric in ('a','b','c','s'):
                self.assertTrue(math.isfinite(float(x[metric])))
            self.assertTrue(0<=float(x['s'])<=1+1e-12)
        self.assertEqual(len(grp),12*2*9)
        for key,items in grp.items():
            self.assertEqual(len(items),128)
            self.assertEqual(len({x['null_seed'] for x in items}),128)
            self.assertEqual(len({x['projector_slice_sha256'] for x in items}),128)
        for d in DEPTHS:
            for seed in SEEDS:
                for choice in ('task_only','joint'):
                    rows=[x for x in obs if (int(x['depth']),int(x['seed']),int(x['rank']),x['observer'])==(d,seed,8,choice)]
                    self.assertEqual(len(rows),2)
                    for row in rows:
                        self.assertEqual(float(row['radius']),.2)
                        self.assertLess(float(row['linear_dark_residual']),.01)
                        self.assertGreater(float(row['finite_isotropic_effect']),0)
                        self.assertTrue(0<=float(row['s'])<=1)
                        self.assertTrue(0<=float(row['p_b_down'])<=1)
                        self.assertLess(float(row['holm_q_s_up']),.051)
        for seed in SEEDS:
            def mean(name,arm):
                rows=[x for x in obs if int(x['depth'])==32 and int(x['seed'])==seed and int(x['rank'])==8 and x['observer']==arm]
                return sum(float(x[name]) for x in rows)/len(rows)
            self.assertLess(mean('ratio_b','joint'),mean('ratio_b','task_only'))
            self.assertLess(mean('s','joint'),mean('s','task_only'))
            self.assertGreater(mean('task_mse','joint'),mean('task_mse','task_only'))

if __name__=='__main__':unittest.main()