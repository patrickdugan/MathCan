import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

W=Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
class AcceptanceTests(unittest.TestCase):
    def reject_mutation(self,filename,mutate):
        with tempfile.TemporaryDirectory(dir=W) as tmp:
            r=Path(tmp).resolve()
            assert r.is_relative_to(W.resolve())
            for n in ("Hodge.ndjson","verdicts.json","axiom-graph.json","source_export_comparison.json","oxilean.exit-code"):
                shutil.copy2(W/"replay432/Hodge"/n,r/n)
            p=r/filename; data=json.loads(p.read_text()); mutate(data)
            p.write_text(json.dumps(data),encoding="utf-8")
            env=dict(os.environ,REPLAY_OUT=str(r))
            run=subprocess.run([sys.executable,str(W/"accept_hodge432.py")],env=env,capture_output=True,text=True)
            self.assertNotEqual(run.returncode,0)
    def test_zero_exit_with_unsupported_target_is_refused(self):
        def mutate(d):
            next(x for x in d["decls"] if x["name"]=="MathCan.Hodge.closed_path_gauge")["verdict"]="unsupported"
        self.reject_mutation("verdicts.json",mutate)
    def test_omitted_dependency_verdict_is_refused(self):
        self.reject_mutation("verdicts.json",lambda d:d["decls"].pop(0))
    def test_changed_export_hash_is_refused(self):
        self.reject_mutation("verdicts.json",lambda d:d["input"].update(sha256="0"*64))
    def test_changed_proof_is_refused(self):
        self.reject_mutation("source_export_comparison.json",lambda d:d["records"][-1].update(value_equal_after_metadata_normalization=False))
    def test_unexpected_axiom_is_refused(self):
        self.reject_mutation("axiom-graph.json",lambda d:d["axioms"].append({"name":"sorryAx"}))

if __name__=="__main__": unittest.main(verbosity=2)
