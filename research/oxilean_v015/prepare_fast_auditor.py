from pathlib import Path
W = Path(__file__).resolve().parent
source = (W/'audit_export.py').read_text(encoding='utf-8')
old = 'selected_missing=set().union(*(nodes[i]["refs"]-owners.keys() for i in closure)) if closure else set()'
new = 'selected_missing={ref for i in closure for ref in nodes[i]["refs"] if ref not in owners}'
assert source.count(old) == 1
(W/'audit_export_fast.py').write_text(source.replace(old, new), encoding='utf-8', newline='\n')
test = (W/'MathCan/research/oxilean_v015/test_audit_export.py').read_text(encoding='utf-8')
test = test.replace('from audit_export import audit', 'from audit_export_fast import audit\nfrom audit_export import audit as original_audit')
extra = '''
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
            path.write_text("\\n".join(map(json.dumps,rows)))
            self.assertTrue(audit(path,"t")["structurally_closed"])
            self.assertFalse(audit(path)["structurally_closed"])
            self.assertEqual(audit(path,"t"),original_audit(path,"t"))
            self.assertEqual(audit(path),original_audit(path))

'''
test = test.replace('if __name__=="__main__":', extra+'if __name__=="__main__":')
(W/'test_audit_export_fast.py').write_text(test, encoding='utf-8', newline='\n')
print('Prepared one-line audit optimization and seven equivalence/control tests.')
