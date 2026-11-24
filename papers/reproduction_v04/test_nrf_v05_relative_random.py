"""Recompute NRF v0.5 random baselines and per-study thresholds from public CSVs."""
import unittest
from pathlib import Path
from nrf_v05_relative_random import build, SCORES, SEEDS

class PublicPaperAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[1]
        if not (root / 'NRF_v04_bidirectional_per_seed.csv').is_file():
            root = root / 'NRF_v04_public'
        cls.rows, cls.report = build(root)
        cls.table = {(r['depth'],r['arm']):r for r in cls.report['group_means']}

    def test_sample_and_reference(self):
        self.assertEqual(len(self.rows),36)
        self.assertEqual(self.report['n_per_state_rows'],1584)
        self.assertEqual(tuple(sorted({r['seed'] for r in self.rows})),SEEDS)
        random=self.table[32,'random_mean']
        self.assertAlmostEqual(random['incoming'],0.717794,places=6)
        self.assertAlmostEqual(random['outgoing'],0.715652,places=6)
        self.assertAlmostEqual(random['within_change'],0.321071,places=6)

    def test_selected_and_task_only_geometry(self):
        sup,task,joint=(self.table[32,arm] for arm in ('supervised','task_only','joint'))
        self.assertAlmostEqual(sup['incoming_over_random_mean'],1.165174,places=5)
        self.assertAlmostEqual(sup['outgoing_over_random_mean'],0.833398,places=5)
        self.assertAlmostEqual(sup['within_change_over_random_mean'],0.547941,places=5)
        self.assertAlmostEqual(task['incoming_over_random_mean'],0.714462,places=5)
        self.assertAlmostEqual(task['outgoing_over_random_mean'],1.084571,places=5)
        self.assertAlmostEqual(task['within_change_over_random_mean'],1.78678,places=5)
        self.assertAlmostEqual(joint['incoming_over_random_mean'],0.442453,places=5)
        self.assertAlmostEqual(joint['outgoing_over_random_mean'],1.068807,places=5)
        self.assertAlmostEqual(joint['within_change_over_random_mean'],1.296626,places=5)
        for name in ('supervised','task_only'):
            r=self.table[32,name]
            self.assertEqual(sum(1 for k in ('incoming','outgoing','within') if r[f'arm_above_all_random_{k}']+r[f'arm_below_all_random_{k}']==6),3)
        self.assertEqual(joint['arm_above_all_random_outgoing'],4)
        self.assertEqual(joint['arm_below_all_random_within'],2)

    def test_depth16_reference(self):
        rand=self.table[16,'random_mean']
        self.assertAlmostEqual(rand['incoming'],0.409401,places=6)
        self.assertAlmostEqual(rand['outgoing'],0.407259,places=6)
        self.assertAlmostEqual(rand['within_change'],0.163648,places=6)
        self.assertAlmostEqual(self.table[16,'joint']['incoming_over_random_mean'],0.770397,places=5)

    def test_depth_break_even_both_cohorts(self):
        crossings={(r['study'],r['depth']):r['break_even_lambda'] for r in self.report['break_evens']}
        for key,want in [(('NRF10',16),0.677621), (('NRF11',16),0.614798),
                         (('NRF10',32),0.624215),(('NRF11',32),0.566663)]:
            self.assertAlmostEqual(crossings[key],want,places=6)

    def test_two_high_gamma_seeds(self):
        by_seed={s['seed']:s for s in self.report['depth32_selected_seed_details']}
        self.assertEqual({s for s in SEEDS if by_seed[s]['gamma']==1},{131,149})
        self.assertAlmostEqual(by_seed[131]['joint_vs_task_MSE_ratio'],1.850762,places=5)
        self.assertAlmostEqual(by_seed[149]['joint_vs_task_MSE_ratio'],1.791350,places=5)
        self.assertAlmostEqual(by_seed[131]['joint_within_over_random'],0.648545,places=5)
        self.assertAlmostEqual(by_seed[149]['joint_within_over_random'],0.886432,places=5)
        self.assertFalse(by_seed[131]['joint_fraction_improves'])
        self.assertEqual(sum(s['joint_fraction_improves'] for s in by_seed.values()),5)

if __name__=='__main__': unittest.main()
