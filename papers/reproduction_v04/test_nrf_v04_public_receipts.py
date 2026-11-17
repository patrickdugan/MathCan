"""Standard-library checks for public NRF v0.4 numerical review receipts.

Run from any directory: python test_nrf_v04_public_receipts.py
This tests exact accounting/normalization of the *published outputs*.
Neural checkpoint recreation requires PyTorch and the archive listed in README.
"""
import csv, json, math, unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE if (HERE/'NRF_v04_bidirectional_per_state.csv').exists() else HERE.parent

def read(path):
    with (BASE/path).open(newline='',encoding='utf-8') as f:
        return list(csv.DictReader(f))

class PublicReviewReceipts(unittest.TestCase):
    def test_two_offdiagonal_energies_all_arms(self):
        data=read('NRF_v04_bidirectional_per_state.csv')
        self.assertEqual(len(data),2*6*12*11)
        for r in data:
            b,c,a,w,v=map(lambda x:float(r[x]),('incoming','outgoing','within_change','write_change','origin_change'))
            self.assertAlmostEqual(w*w,b*b+a*a,places=9)
            self.assertAlmostEqual(v*v,c*c+a*a,places=9)
            self.assertTrue(0<=float(r['incoming_fraction'])<=1+1e-10)
            self.assertTrue(0<=float(r['outgoing_fraction'])<=1+1e-10)

    def test_seed_average_recomputes(self):
        data=read('NRF_v04_bidirectional_per_state.csv')
        means=read('NRF_v04_bidirectional_per_seed.csv')
        self.assertEqual(len(means),12*11)
        for row in means:
            arm=row['arm'];depth=row['depth'];seed=row['seed']
            sub=[r for r in data if (r['arm'],r['depth'],r['seed'])==(arm,depth,seed)]
            self.assertEqual(len(sub),12)
            for name in ('incoming','outgoing','within_change','write_change','origin_change','incoming_fraction','outgoing_fraction'):
                self.assertAlmostEqual(float(row[name]),sum(float(r[name]) for r in sub)/12,places=11)

    def test_selected_gammas_and_direction(self):
        data=read('NRF_v04_bidirectional_per_seed.csv')
        self.assertEqual(sum(1 for x in data if x['depth']=='32' and x['arm']=='joint' and float(x['incoming'])<float(x['outgoing'])),6)
        improved=0
        for seed in ('131','137','139','149','151','157'):
            task=next(r for r in data if r['seed']==seed and r['depth']=='32' and r['arm']=='task_only')
            joint=next(r for r in data if r['seed']==seed and r['depth']=='32' and r['arm']=='joint')
            improved+=float(joint['incoming_fraction'])<float(task['incoming_fraction'])
        self.assertEqual(improved,5)

    def test_frontier_and_original_thresholds(self):
        a=json.loads((BASE/'NRF_v04_envelope_summary.json').read_text())
        values=[r['start'] for r in a['lower_envelope']][1:]
        expected=(0.13647448374771712,0.8758038494708656,1.2426648699344243,1.3917169449939497)
        for val,exp in zip(values,expected):self.assertAlmostEqual(val,exp,places=11)
        self.assertAlmostEqual(a['selected_thresholds']['NRF10']['lambda'],0.6242151730789396,places=11)
        self.assertAlmostEqual(a['selected_thresholds']['NRF11']['lambda'],0.5666626070929325,places=11)

    def test_selected_risk_reconstructable(self):
        rows=read('NRF_v04_selected_observer_risk.csv')
        self.assertEqual(len(rows),24)
        for item in rows:
            for a in ('task_only','joint'):
                score=float(item[a+'_MSE'])+float(item[a+'_leakage'])**2
                self.assertAlmostEqual(score,float(item[a+'_objective']),places=11)

if __name__=='__main__':unittest.main()
