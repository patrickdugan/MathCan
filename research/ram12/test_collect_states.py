"""RAM-12 software contracts; only GitHub native run supplies Lean state evidence."""
from __future__ import annotations
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent))
from collect_states import read_expected, split, instrument, read_markers, aggregate, source_for_case

HERE=Path(__file__).resolve().parent

class RAM12Contracts(unittest.TestCase):
    def test_exact_immutable_worklist_inventory(self):
        cases=read_expected(HERE.parent/'ram11f'/'locked_worklist.jsonl')
        self.assertEqual(len(cases),76)
        self.assertEqual(sum(len(x['proposed_new_actions']) for x in cases),282)
        roots={(x['source_file'],x['theorem']) for x in cases}
        self.assertEqual(len(roots),22)
        self.assertEqual({g:sum(split(*r)==g for r in roots) for g in ('train','dev','holdback')},
                         {'train':14,'dev':3,'holdback':5})
    def test_tactic_positions_preserved(self):
        x=instrument(['intro ram07_arg0','exact h'],'RAM11F-009')
        self.assertEqual(x,['ram12_observe "RAM11F-009:00"','intro ram07_arg0',
                            'ram12_observe "RAM11F-009:01"','exact h'])
    def test_valid_full_native_goals(self):
        parts=[dict(id='RAM11F-000:00',goals=['h : True\n⊢ True'],definitions=['MathCan.x']),
               dict(id='RAM11F-000:01',goals=['⊢ True'],definitions=[])]
        log=''.join('sample.lean:3:7: info: RAM12_STATE_JSON:'+json.dumps(x,ensure_ascii=False)+'\n' for x in parts)
        self.assertEqual(read_markers(log,'RAM11F-000',['intro','exact h']),parts)
        with self.assertRaises(ValueError):read_markers(log,'RAM11F-000',['intro'])
        with self.assertRaises(ValueError):read_markers(log.replace('RAM11F-000:01','RAM11F-000:04'),'RAM11F-000',['intro','exact h'])
    def test_reject_same_prefix_divergent_goals(self):
        r=dict(source_file='MathCan/F.lean',theorem='x',proof_id='RAM11F-000',
               prefix_actions=[],next_action='constructor',goals=['⊢ True ∧ True'],
               definitions=[],split='train')
        with self.assertRaisesRegex(AssertionError,'conflicting Lean states'):
            aggregate([r,dict(r,proof_id='RAM11F-001',goals=['⊢ True'])])
    def test_original_proof_replaced_no_admitted_tactic(self):
        original=b'namespace MathCan\ntheorem x (h : True) : True := h\nend MathCan\n'
        text=source_for_case(original,'x',['exact h'],'RAM11F-000').decode()
        self.assertIn('ram12_observe "RAM11F-000:00"',text)
        self.assertIn('  exact h',text)
        self.assertNotIn('True := h',text)
        self.assertNotIn('sorry',text)
        self.assertIn('import RAM12.Trace',text)
    def test_original_public_source_only(self):
        text=(HERE/'PREREGISTRATION.md').read_text()
        self.assertIn('c84e2025334e9a967c1297425a490f98d5b3d189',text)
        self.assertIn('76',text)
        self.assertIn('not',text.lower())

if __name__=='__main__': unittest.main()
