import json
import os
from pathlib import Path
import tempfile
import unittest
from audit_export_fast import audit
from audit_export import audit as original_audit

ROOT=Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
class AuditTests(unittest.TestCase):
    def test_positive_bundle_closure(self):
        r=audit(ROOT/"oxilean/tests/fixtures/lean4export/ProjRecIndexed.ndjson")
        self.assertTrue(r["structurally_closed"])
        self.assertTrue(r["unambiguous_names"])
    def test_distinguishes_flat_and_hierarchical_name(self):
        r=audit(ROOT/"oxilean/tests/fixtures/lean4export/RecNameMixedStyle.ndjson")
        allnames=[x for n in r["records"] for x in n["names"]]
        self.assertIn([["str","A"],["str","rec"]],allnames)
        self.assertIn([["str","A.rec"]],allnames)
        self.assertFalse(r["structurally_closed"])
    def test_duplicate_name_is_not_overwritten(self):
        r=audit(ROOT/"oxilean/tests/fixtures/lean4export/RecNameMixedStyleTruth.ndjson")
        self.assertFalse(r["unambiguous_names"])
        self.assertEqual(len(r["duplicate_names"]),1)
    def test_unknown_expression_is_fail_closed(self):
        with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
            p=Path(tmp)/"bad.ndjson"
            p.write_text(json.dumps({"meta":{"format":{"version":"3.1.0"}}})+"\n"+json.dumps({"ie":0,"app":{"fn":999,"arg":999}})+"\n")
            with self.assertRaises(KeyError): audit(p)
    def test_axioms_and_type_dependencies(self):
        rows=[{"meta":{"format":{"version":"3.1.0"}}},
              {"in":1,"str":{"pre":0,"str":"A"}},
              {"in":2,"str":{"pre":0,"str":"t"}},
              {"ie":0,"sort":0},
              {"axiom":{"name":1,"type":0,"isUnsafe":False,"levelParams":[]}},
              {"ie":1,"const":{"name":1,"us":[]}},
              {"thm":{"name":2,"type":1,"value":1,"all":[2],"levelParams":[]}}]
        with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
            p=Path(tmp)/"axiom.ndjson"; p.write_text("\n".join(map(json.dumps,rows)))
            r=audit(p,"t")
            self.assertEqual(r["closure_record_count"],2)
            self.assertEqual([x["name"] for x in r["axioms"]],["A"])


    def test_exact_equivalence_on_existing_fixtures(self):
        for path in (ROOT/"oxilean/tests/fixtures/lean4export").glob("*.ndjson"):
            with self.subTest(path=path.name):
                try:
                    expected=original_audit(path)
                except Exception as ex:
                    with self.assertRaises(type(ex)) as caught:
                        audit(path)
                    self.assertEqual(str(caught.exception), str(ex))
                else:
                    self.assertEqual(audit(path), expected)

    def test_target_scope_excludes_unrelated_missing_reference(self):
        rows=[{"meta":{"format":{"version":"3.1.0"}}},
              {"in":1,"str":{"pre":0,"str":"A"}},
              {"in":2,"str":{"pre":0,"str":"t"}},
              {"in":3,"str":{"pre":0,"str":"missing"}},
              {"in":4,"str":{"pre":0,"str":"unrelated"}},
              {"ie":0,"sort":0},
              {"axiom":{"name":1,"type":0,"levelParams":[]}},
              {"ie":1,"const":{"name":1,"us":[]}},
              {"thm":{"name":2,"type":1,"value":1,"levelParams":[]}},
              {"ie":2,"const":{"name":3,"us":[]}},
              {"thm":{"name":4,"type":2,"value":2,"levelParams":[]}}]
        with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
            path=Path(tmp)/"scoped.ndjson"
            path.write_text("\n".join(map(json.dumps,rows)))
            self.assertTrue(audit(path,"t")["structurally_closed"])
            self.assertFalse(audit(path)["structurally_closed"])
            self.assertEqual(audit(path,"t"),original_audit(path,"t"))
            self.assertEqual(audit(path),original_audit(path))

if __name__=="__main__": unittest.main(verbosity=2)
