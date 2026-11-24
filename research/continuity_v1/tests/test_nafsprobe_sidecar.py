"""CPU tests for immutable source and append-only observation-sidecar semantics."""
import hashlib
from contextlib import closing
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest

from research.continuity_v1.nafsprobe_sidecar import audit_sidecar, sync_nafsprobe
from test_nafsprobe_bridge import example_snapshot, write_legacy_db


class SidecarTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.source = Path(self.temp.name) / "nafsprobe.sqlite3"
        self.sidecar = Path(self.temp.name) / "observed.sqlite3"
        write_legacy_db(self.source)

    def update_source(self, state):
        with closing(sqlite3.connect(self.source)) as db, db:
            db.execute("UPDATE agent_state SET payload=? WHERE run_id='sample'",
                       (json.dumps(state, ensure_ascii=False),))

    def test_source_read_only_and_idempotent_sync(self):
        original_hash = hashlib.sha256(self.source.read_bytes()).hexdigest()
        first = sync_nafsprobe(self.source, "sample", self.sidecar)
        second = sync_nafsprobe(self.source, "sample", self.sidecar)
        self.assertEqual(first.status, "appended")
        self.assertEqual(second.status, "unchanged")
        self.assertEqual(first.chain_tip, second.chain_tip)
        self.assertEqual(first.event_count, second.event_count)
        self.assertEqual(hashlib.sha256(self.source.read_bytes()).hexdigest(), original_hash)
        self.assertEqual(audit_sidecar(self.sidecar, "sample").chain_tip, first.chain_tip)

    def test_structured_change_is_recorded_as_retract_and_assert(self):
        first = sync_nafsprobe(self.source, "sample", self.sidecar)
        state = example_snapshot()
        state["beliefs"]["bridge"]["value"] = "open"
        state["commitments"] = {}
        self.update_source(state)
        second = sync_nafsprobe(self.source, "sample", self.sidecar)
        self.assertEqual(second.observation_seq, 1)
        self.assertNotEqual(second.canonical_claims_sha256, first.canonical_claims_sha256)
        self.assertEqual(second.status, "appended")
        self.assertEqual(audit_sidecar(self.sidecar, "sample").chain_tip, second.chain_tip)
        with closing(sqlite3.connect(self.sidecar)) as db, db:
            kinds = [json.loads(r[0])["kind"] for r in db.execute("SELECT event_json FROM continuity_events WHERE run_id='sample' ORDER BY pos")]
        self.assertEqual(kinds.count("retract"), 2)
        self.assertEqual(kinds.count("assert"), 4)  # 3 original, 1 new belief

    def test_only_reflection_changes(self):
        before = sync_nafsprobe(self.source, "sample", self.sidecar)
        state = example_snapshot()
        state["reflections"][0]["text"] = "Another interpretation (not an authorization)"
        self.update_source(state)
        after = sync_nafsprobe(self.source, "sample", self.sidecar)
        self.assertEqual(after.canonical_claims_sha256, before.canonical_claims_sha256)
        self.assertNotEqual(after.chain_tip, before.chain_tip)
        self.assertGreater(after.event_count, before.event_count)
        self.assertEqual(audit_sidecar(self.sidecar, "sample").chain_tip, after.chain_tip)

    def test_repeat_revisions_and_return_to_original_state(self):
        original = example_snapshot()
        initial = sync_nafsprobe(self.source,"sample",self.sidecar)
        expected_initial_digest = initial.canonical_claims_sha256
        for k in range(1, 9):
            update = example_snapshot()
            update["beliefs"]["bridge"]["value"] = "open" if k % 2 else "closed"
            if k % 3 == 0:
                update["commitments"].clear()
            update["reflections"][0]["text"] = f"reviewed version {k}"
            self.update_source(update)
            seen = sync_nafsprobe(self.source,"sample",self.sidecar)
            self.assertEqual(seen.observation_seq, k)
            self.assertEqual(audit_sidecar(self.sidecar,"sample").chain_tip,seen.chain_tip)
        self.update_source(original)
        restored = sync_nafsprobe(self.source,"sample",self.sidecar)
        self.assertEqual(restored.observation_seq, 9)
        self.assertEqual(restored.canonical_claims_sha256, expected_initial_digest)
        self.assertNotEqual(restored.chain_tip, initial.chain_tip)

    def test_different_runs_have_separate_chains(self):
        with closing(sqlite3.connect(self.source)) as db, db:
            db.execute("INSERT INTO agent_state VALUES (?, ?)",
                       ("other", json.dumps(example_snapshot(), ensure_ascii=False)))
        a = sync_nafsprobe(self.source,"sample",self.sidecar)
        b = sync_nafsprobe(self.source,"other",self.sidecar)
        self.assertEqual(a.observation_seq,0)
        self.assertEqual(b.observation_seq,0)
        self.assertEqual(a.canonical_claims_sha256,b.canonical_claims_sha256)
        self.assertEqual(audit_sidecar(self.sidecar,"sample").chain_tip,a.chain_tip)
        self.assertEqual(audit_sidecar(self.sidecar,"other").chain_tip,b.chain_tip)

    def test_rejects_destination_equalling_source(self):
        with self.assertRaises(ValueError):
            sync_nafsprobe(self.source,"sample",self.source)

    def test_external_tamper_detected(self):
        sync_nafsprobe(self.source,"sample",self.sidecar)
        with closing(sqlite3.connect(self.sidecar)) as db, db:
            db.execute("UPDATE continuity_events SET event_json='{}' WHERE pos=0")
        with self.assertRaises(ValueError):
            audit_sidecar(self.sidecar,"sample")

    def test_commandline_audit_after_process_restart(self):
        expected = sync_nafsprobe(self.source,"sample",self.sidecar)
        proc = subprocess.run([sys.executable,"-m","research.continuity_v1.nafsprobe_sidecar",
                               "--sidecar",str(self.sidecar),"--run-id","sample","--audit-only"],
                              cwd=Path(__file__).resolve().parents[3],capture_output=True,text=True,check=True)
        out = json.loads(proc.stdout)
        self.assertEqual(out["status"],"audited")
        self.assertEqual(out["chain_tip"],expected.chain_tip)
        self.assertNotIn("clinic",proc.stdout)


if __name__ == "__main__":
    unittest.main()
