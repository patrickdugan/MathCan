"""ROC-01 tests of PUBLIC NRF11 source replay and exact observed frontier."""
import csv
import hashlib
import json
from pathlib import Path
import unittest

from research.observer_calculus.nrf_retrofit import produce, read_rows
from research.observer_calculus.frontier import (
    lower_envelope, stringify_envelope, pareto_surface, inherited_v04_check)

P=Path("research/observer_calculus")


class TestNRFRetrofit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original_state=read_rows(Path("papers/NRF_v04_bidirectional_per_state.csv"))
        cls.original_risk=read_rows(Path("papers/NRF_v04_selected_observer_risk.csv"))
        cls.old_env=json.loads(Path("papers/NRF_v04_envelope_summary.json").read_text())
        cls.state,cls.seeds,cls.report=produce(
            cls.original_state,cls.original_risk,cls.old_env)

    def test_original_public_inputs_pinned(self):
        expected={
          "papers/NRF_v04_bidirectional_per_state.csv":
            "bcb0e702642dee2882cdb9ffcf3c61dcec7bd4e5",
          "papers/NRF_v04_selected_observer_risk.csv":
            "dbcd439c70f243b8faa0ed634d3066c035ccc5df",
          "papers/NRF_v04_envelope_summary.json":
            "531617080d4b7b4a1f6dd4113fde3c352cffbf94",
        }
        for name,reference in expected.items():
            raw=Path(name).read_bytes()
            actual=hashlib.sha1(
                b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()
            self.assertEqual(actual,reference)

    def test_per_state_1584_and_partial_card_truthfulness(self):
        self.assertEqual(len(self.state),1584)
        self.assertEqual(len(self.seeds),12)
        self.assertEqual(len({(x["depth"],x["seed"],x["arm"],x["state_index"])
                              for x in self.state}),1584)
        self.assertTrue(all(x["card_status"]=="retrospective_partial" for x in self.state))
        self.assertTrue(all(x["s_causal"]=="" and x["A_normalized"]==""
                             and x["task_mse_state"]=="" and x["rank_p"]==""
                             for x in self.state))
        self.assertTrue(all(x["null_count"]=="8" and x["rank_p_valid"]=="False"
                             for x in self.state))

    def test_published_per_state_rows_replay(self):
        original=read_rows(P/"ROC01_NRF11_PER_STATE_PARTIAL.csv")
        self.assertEqual(len(original),len(self.state))
        for result,expected in zip(self.state,original):
            for k,v in result.items():
                if k in ("A_frob_per_sqrtk","B_frob_per_sqrtk",
                         "C_frob_per_sqrtk","W_delta_per_sqrtk","rho_delta"):
                    self.assertAlmostEqual(float(v),float(expected[k]),delta=1e-11)
                else:
                    self.assertEqual(str(v),expected[k])

    def test_six_model_seed_shapley_identity(self):
        for depth in (16,32):
            cards=[r for r in self.seeds if r["depth"]==depth]
            self.assertEqual(len(cards),6)
            for x in cards:
                self.assertAlmostEqual(x["delta_B"],
                   x["magnitude_contribution"]+x["fraction_contribution"],delta=1e-12)
                self.assertLess(x["delta_B"],0)
        a=self.report["by_depth"]["32"]
        self.assertEqual(a["counts"]["B_decreases"],6)
        self.assertEqual(a["counts"]["write_magnitude_contribution_negative"],6)
        self.assertEqual(a["counts"]["dark_fraction_contribution_negative"],5)
        self.assertAlmostEqual(a["means"]["magnitude_contribution"],-0.1617370603181253,places=12)
        self.assertAlmostEqual(a["means"]["fraction_contribution"],-0.03350953627692834,places=12)
        self.assertEqual({int(r["seed"]):r["gamma"] for r in self.seeds
                          if r["depth"]==32}[131],1.)
        self.assertEqual({int(r["seed"]):r["gamma"] for r in self.seeds
                          if r["depth"]==32}[149],1.)

    def test_published_seed_rows_are_source_reproducible(self):
        original=read_rows(P/"ROC01_NRF11_PER_SEED_DECOMP.csv")
        self.assertEqual(len(original),12)
        for expected,observed in zip(original,self.seeds):
            for key,val in observed.items():
                if isinstance(val,(float,int)):
                    self.assertAlmostEqual(float(expected[key]),float(val),delta=1e-11)
                else:
                    self.assertEqual(expected[key],val)
        on_disk=json.loads((P/"ROC01_NRF11_SUMMARY.json").read_text())
        self.assertEqual(on_disk["schema"],self.report["schema"])
        self.assertEqual(on_disk["by_depth"]["32"]["counts"],
                         self.report["by_depth"]["32"]["counts"])

    def test_old_raw_lower_envelope_remains_distinct(self):
        actual=inherited_v04_check()
        self.assertEqual(len(actual),5)
        self.assertEqual([x["winner"] for x in actual],
            ["gamma=0","gamma=0.05","gamma=0.2","gamma=1",
             "task_free_supervised_start"])
        self.assertAlmostEqual(actual[1]["start"],0.13647448374771715,places=12)
        self.assertAlmostEqual(actual[2]["start"],0.875803849470866,places=12)
        self.assertAlmostEqual(actual[3]["start"],1.2426648699344234,places=12)
        self.assertAlmostEqual(actual[4]["start"],1.39171694499395,places=12)

    def test_exact_envelope_ignores_dominated_pairwise_intersections(self):
        result=stringify_envelope(lower_envelope({
            "task":(0,2),"balanced":(1,1),"low_leak":(4,0),
            "dominated":(3,2)}))
        self.assertEqual(result[0]["winner"],"task")
        self.assertEqual([r["winner"] for r in result],
                         ["task","balanced","low_leak"])
        self.assertEqual([r["start"] for r in result],[0.,1.,3.])

    def test_rank_error_coupling_surface(self):
        q=pareto_surface([
            {"id":"a","rank":2,"task_error":0.3,"normalized_B":0.1},
            {"id":"b","rank":4,"task_error":0.2,"normalized_B":0.05},
            {"id":"dominated","rank":8,"task_error":0.4,"normalized_B":0.2},
            {"id":"high_cap","rank":8,"task_error":0.1,"normalized_B":0.06}])
        self.assertEqual(q["pareto"],["a","b","high_cap"])
        self.assertEqual(q["dominated"],["dominated"])
        with self.assertRaises(ValueError):
            pareto_surface([{"id":"broken","rank":8,"task_error":0.1}])

if __name__=="__main__":
    unittest.main()
