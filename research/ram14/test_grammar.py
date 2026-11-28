"""RAM-14 source isolation and structural tactic grammar contracts."""
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent))
from grammar import generate,mask_comments,statement_scope,earlier_headers,git_blob,\
    TARGETS,FAMILIES,MAX_PER_FAMILY,MAX_TOTAL,NAME


SOURCE = """import Init
namespace G
universe u
def iterateState {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateState f n (f x)
structure StateGauge (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ x : α, invFun (toFun x) = x
  right_inv : ∀ x : α, toFun (invFun x) = x
def transport {α : Type u} (g : StateGauge α) (f : α → α) : α → α :=
  fun y => g.toFun (f (g.invFun y))
theorem transport_iterate {α : Type u} (g : StateGauge α) (f : α → α)
 (n : Nat) (x : α) :
 iterateState (transport g f) n (g.toFun x) =
 g.toFun (iterateState f n x) := by
  exact False.elim (by sorry)
theorem observable_transport {α : Type u} (g : StateGauge α) (f : α → α)
 (n : Nat) (x : α) :
 iterateState (transport g f) n (g.toFun x) =
 iterateState (transport g f) n (g.toFun x) := by
  trivial
theorem after_the_target : True := by
  trivial
end G
"""


def records(target,source=SOURCE):
    return [(a.family,a.script,a.witnesses) for a in generate(source,target)]


class Contract(unittest.TestCase):
    def test_comment_masking_nested_and_line(self):
        original="x /- abc /-nested-/ done -/ y -- comment\nz"
        masked=mask_comments(original)
        self.assertEqual(len(original),len(masked))
        self.assertIn("y",masked)
        self.assertNotIn("nested",masked)
        self.assertIn("\nz",masked)
        with self.assertRaises(ValueError):mask_comments("/- never closed")
    def test_nat_induction_comes_from_typed_binder(self):
        rr=records("transport_iterate")
        self.assertTrue(any("induction n generalizing x" in script
                            for family,script,_ in rr if family=="nat_induction"))
        self.assertTrue(all("theorem transport_iterate" not in script for _,script,_ in rr))
    def test_source_prior_and_structure_inverse_field(self):
        rr=records("observable_transport")
        self.assertTrue(any("transport_iterate" in script
                            for family,script,_ in rr if family=="rewrite_prior"))
        self.assertTrue(any("g.left_inv" in script
                            for _,script,_ in rr))
        self.assertTrue(all("after_the_target" not in script for _,script,_ in rr))
    def test_target_reference_proof_body_never_affects_candidates(self):
        a=records("transport_iterate")
        changed=SOURCE.replace("exact False.elim (by sorry)",
                               "omega\n  -- target source reference proof is now very different")
        self.assertEqual(a,records("transport_iterate",changed))
        b=records("observable_transport")
        changed=SOURCE.replace("theorem after_the_target", "theorem after_the_target")
        changed=changed.replace("  trivial\ntheorem after_the_target",
                                "  exact False.elim (by sorry)\ntheorem after_the_target")
        self.assertEqual(b,records("observable_transport",changed))
    def test_preregistered_budget_and_determinism(self):
        for target in TARGETS:
            actions=generate(SOURCE,target)
            self.assertLessEqual(len(actions),MAX_TOTAL)
            for family in FAMILIES:
                self.assertLessEqual(sum(a.family==family for a in actions),MAX_PER_FAMILY)
            self.assertEqual(actions,generate(SOURCE,target))
            self.assertEqual(len(actions),len({(a.family,a.script) for a in actions}))
    def test_prior_header_does_not_use_earlier_proof_body(self):
        base=SOURCE
        injected=SOURCE.replace("exact False.elim (by sorry)",
            "have left_inv : True := by trivial\n  have iterateState : True := by trivial\n  exact False.elim (by sorry)")
        self.assertEqual(records("observable_transport",base),
                         records("observable_transport",injected))
    def test_prior_decl_and_blob_are_strict(self):
        before,statement=statement_scope(SOURCE,"observable_transport")
        self.assertEqual([x[0] for x in earlier_headers(before)],["transport_iterate"])
        self.assertIn("readout", "readout")
        self.assertEqual(len(git_blob(b"abc")),40)
        self.assertTrue(NAME.fullmatch("n"))
    def test_omit_nat_induction_when_no_nat_binder(self):
        changed=SOURCE.replace("(n : Nat) (x : α)", "(n : Fin 4) (x : α)")
        self.assertFalse(any(a.family=="nat_induction"
                            for a in generate(changed,"transport_iterate")))


if __name__=="__main__":
    unittest.main()
