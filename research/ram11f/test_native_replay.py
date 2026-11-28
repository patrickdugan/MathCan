"""Software-only self-tests. Native theorem results require separate Lean4.35 CI."""
import tempfile,unittest
from pathlib import Path
from native_replay import render_source,axiom_inventory,validate_worklist,sha,WORKLIST_HASH

EXAMPLE='''import Init
namespace MathCan.Hodge

theorem foo (h : True) : True := by
  have deeper : True := by
    trivial
  exact deeper

/-- subsequent theorem remains untouched -/
theorem bar : True := by
  trivial

#print axioms foo
end MathCan.Hodge
'''

class NativeReplayTests(unittest.TestCase):
    def test_worklist_original_sha_and_unique_all_cases(self):
        path=Path(__file__).with_name('locked_worklist.jsonl')
        self.assertEqual(sha(path.read_bytes()),WORKLIST_HASH)
        rows=validate_worklist(path)
        self.assertEqual(len(rows),76)
        self.assertEqual(len({(x['source_file'],x['theorem']) for x in rows}),22)
        self.assertTrue(all(x['historical_proof_score']==0 for x in rows))

    def test_replaced_proof_removes_original_tactics_and_nested_have(self):
        result=render_source(EXAMPLE,'foo',['exact h'])
        self.assertIn('theorem foo (h : True) : True := by\n  exact h',result)
        self.assertNotIn('have deeper',result)
        self.assertIn('theorem bar : True := by\n  trivial',result)
        self.assertIn('#print axioms foo',result)
        self.assertIn('end MathCan.Hodge',result)

    def test_retain_multiline_header(self):
        source='''namespace X

theorem alpha
    (x : Nat)
    (h : x=x) :
    x=x := by
  rfl

#print axioms alpha
end X
'''
        result=render_source(source,'alpha',['exact h'])
        self.assertIn('theorem alpha\n    (x : Nat)\n    (h : x=x) :\n    x=x := by\n  exact h',result)
        self.assertNotIn('  rfl',result)

    def test_term_style_original_proof_replaced_without_reference_term(self):
        source='''namespace X

theorem term_demo (h : True) : True := h

theorem later : True := by
  trivial
end X
'''
        result=render_source(source,'term_demo',['exact h'])
        self.assertIn('theorem term_demo (h : True) : True := by\n  exact h',result)
        self.assertNotIn('True := h',result)
        self.assertIn('theorem later : True := by\n  trivial',result)

    def test_missing_root_denied(self):
        with self.assertRaises(ValueError):render_source(EXAMPLE,'unrelated',['rfl'])

    def test_missing_proof_marker_denied(self):
        with self.assertRaises(ValueError):render_source('theorem X : True\n','X',['rfl'])

    def test_axiom_inventory_empty(self):
        log='RAM11F_AXIOMS_BEGIN_20261115\n\'MathCan.foo\' does not depend on any axioms\nRAM11F_AXIOMS_END_20261115\n'
        self.assertEqual(axiom_inventory(log),(True,[],''))

    def test_axiom_inventory_allowed(self):
        log='RAM11F_AXIOMS_BEGIN_20261115\n\'MathCan.foo\' depends on axioms: [propext, Classical.choice]\nRAM11F_AXIOMS_END_20261115\n'
        self.assertEqual(axiom_inventory(log),(True,['propext','Classical.choice'],''))

    def test_axiom_inventory_rejects_admission(self):
        log='RAM11F_AXIOMS_BEGIN_20261115\n\'MathCan.foo\' depends on axioms: [sorryAx]\nRAM11F_AXIOMS_END_20261115\n'
        okay,axioms,_=axiom_inventory(log)
        self.assertFalse(okay)
        self.assertEqual(axioms,['sorryAx'])

    def test_axiom_inventory_requires_markers(self):
        self.assertFalse(axiom_inventory("'MathCan.foo' does not depend on any axioms")[0])

if __name__=='__main__':unittest.main()